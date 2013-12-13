//$HeadURL$
/*----------------------------------------------------------------------------
 This file is part of deegree, http://deegree.org/
 Copyright (C) 2001-2011 by:
 - Department of Geography, University of Bonn -
 and
 - lat/lon GmbH -

 This library is free software; you can redistribute it and/or modify it under
 the terms of the GNU Lesser General Public License as published by the Free
 Software Foundation; either version 2.1 of the License, or (at your option)
 any later version.
 This library is distributed in the hope that it will be useful, but WITHOUT
 ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 details.
 You should have received a copy of the GNU Lesser General Public License
 along with this library; if not, write to the Free Software Foundation, Inc.,
 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

 Contact information:

 lat/lon GmbH
 Aennchenstr. 19, 53177 Bonn
 Germany
 http://lat-lon.de/

 Department of Geography, University of Bonn
 Prof. Dr. Klaus Greve
 Postfach 1147, 53001 Bonn
 Germany
 http://www.geographie.uni-bonn.de/deegree/

 e-mail: info@deegree.org
 ----------------------------------------------------------------------------*/
package org.deegree.feature.persistence.sql.insert;

import static org.deegree.feature.Features.findFeaturesAndGeometries;

import java.sql.Connection;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.xml.namespace.QName;

import org.deegree.commons.jdbc.SQLIdentifier;
import org.deegree.commons.jdbc.TableName;
import org.deegree.commons.tom.TypedObjectNode;
import org.deegree.commons.tom.genericxml.GenericXMLElement;
import org.deegree.commons.tom.gml.GMLReferenceResolver;
import org.deegree.commons.tom.gml.property.Property;
import org.deegree.commons.tom.primitive.BaseType;
import org.deegree.commons.tom.primitive.PrimitiveValue;
import org.deegree.commons.tom.sql.ParticleConverter;
import org.deegree.commons.utils.Pair;
import org.deegree.cs.coordinatesystems.ICRS;
import org.deegree.feature.Feature;
import org.deegree.feature.FeatureCollection;
import org.deegree.feature.persistence.BBoxTracker;
import org.deegree.feature.persistence.FeatureStoreException;
import org.deegree.feature.persistence.sql.FeatureTypeMapping;
import org.deegree.feature.persistence.sql.MappedAppSchema;
import org.deegree.feature.persistence.sql.SQLFeatureStore;
import org.deegree.feature.persistence.sql.SQLFeatureStoreTransaction;
import org.deegree.feature.persistence.sql.converter.CustomParticleConverter;
import org.deegree.feature.persistence.sql.converter.FeatureParticleConverter;
import org.deegree.feature.persistence.sql.expressions.TableJoin;
import org.deegree.feature.persistence.sql.id.KeyPropagation;
import org.deegree.feature.persistence.sql.id.TableDependencies;
import org.deegree.feature.persistence.sql.jaxb.CustomConverterJAXB;
//import org.deegree.feature.persistence.sql.insert.FeatureRow;
//import org.deegree.feature.persistence.sql.insert.InsertRowManager;
//import org.deegree.feature.persistence.sql.insert.InsertRow;
import org.deegree.feature.persistence.sql.rules.CompoundMapping;
import org.deegree.feature.persistence.sql.rules.ConstantMapping;
import org.deegree.feature.persistence.sql.rules.FeatureMapping;
import org.deegree.feature.persistence.sql.rules.GeometryMapping;
import org.deegree.feature.persistence.sql.rules.Mapping;
import org.deegree.feature.persistence.sql.rules.PrimitiveMapping;
import org.deegree.feature.types.FeatureType;
import org.deegree.feature.types.property.GeometryPropertyType.CoordinateDimension;
import org.deegree.feature.xpath.TypedObjectNodeXPathEvaluator;
import org.deegree.filter.FilterEvaluationException;
import org.deegree.geometry.Geometry;
import org.deegree.gml.reference.FeatureReference;
import org.deegree.protocol.wfs.transaction.action.IDGenMode;
import org.deegree.protocol.wfs.transaction.action.ParsedPropertyReplacement;
import org.deegree.sqldialect.SQLDialect;
import org.deegree.sqldialect.filter.DBField;
import org.deegree.sqldialect.filter.MappingExpression;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Performs inserts in courtesy of the {@link SQLFeatureStoreTransaction}.
 * <p>
 * Important aspects of the implementation:
 * <ul>
 * <li>Streaming/low memory footprint</li>
 * <li>Usability for complex structures/mappings</li>
 * <li>Coping with unresolved feature references (forward/backward xlinks)</li>
 * <li>Auto-generated feature ids/key columns</li>
 * </ul>
 * 
 * @author <a href="mailto:schneider@lat-lon.de">Markus Schneider</a>
 * @author last edited by: $Author$
 * 
 * @version $Revision$, $Date$
 */
public class InsertRowManager {

    private static Logger LOG = LoggerFactory.getLogger( InsertRowManager.class );

    private SQLFeatureStore fs;

    private final SQLDialect dialect;

    private final Connection conn;

    private final IDGenMode idGenMode;

    private final TableDependencies tableDeps;
    
    private MappedAppSchema mappedschema;

    // key: original feature id (from Feature or FeatureReference), value: feature row
    private final Map<String, FeatureRow> origFidToFeatureRow = new HashMap<String, FeatureRow>();

    // key: insert row, value: dependent rows (never null)
    private final Map<InsertRow, List<InsertRow>> rowToChildRows = new HashMap<InsertRow, List<InsertRow>>();

    // values: rows that have not been inserted yet
    private final Set<InsertRow> delayedRows = new HashSet<InsertRow>();

    // values: rows that have not been inserted yet, but can be inserted (no parents)
    private final Set<InsertRow> rootRows = new HashSet<InsertRow>();
    
    private final Map<Mapping, ParticleConverter<?>> particleMappingToConverter = new HashMap<Mapping, ParticleConverter<?>>();

	private GMLReferenceResolver resolver;
	
	private String tablename;
	
	 /**
     * Creates a new {@link InsertRowManager} instance.
     * 
     * @param fs
     *            feature store, must not be <code>null</code>
     * @param conn
     *            connection, must not be <code>null</code>
     * @param idGenMode
     *            feature id generation mode, must not be <code>null</code>
     */
    public InsertRowManager( SQLFeatureStore fs, Connection conn, IDGenMode idGenMode ) {
        this.fs = fs;
        this.dialect = fs.getDialect();
        this.conn = conn;
        this.idGenMode = idGenMode;
        this.tableDeps = fs.getSchema().getKeyDependencies();
    }

    /**
     * Creates a new {@link InsertRowManager} instance.
     * 
     * @param fs
     *            feature store, must not be <code>null</code>
     * @param conn
     *            connection, must not be <code>null</code>
     * @param idGenMode
     *            feature id generation mode, must not be <code>null</code>
     */
    public InsertRowManager( SQLDialect dialect, Connection conn, IDGenMode idGenMode,MappedAppSchema schema, String tablename ) {
        //this.fs = fs;
        this.dialect = dialect;
        this.conn = conn;
        this.idGenMode = idGenMode;
        this.mappedschema = schema;
        this.tableDeps = schema.getKeyDependencies();
        this.tablename = tablename;
        initConverters();
    }

    /**
     * Inserts the specified feature.
     * <p>
     * Note that some or all of the corresponding table rows may actually not be inserted when this method returns. They
     * may be delayed until their dependencies are inserted. This method also takes care of checking for rows that have
     * been delayed and can be inserted now.
     * </p>
     * 
     * @param feature
     *            feature instance to be inserted, must not be <code>null</code>
     * @param ftMapping
     *            mapping of the corresponding feature type, must not be <code>null</code>
     * @return id of the stored feature, never <code>null</code>
     */
    public FeatureRow insertFeature( Feature feature, FeatureTypeMapping ftMapping )
                            throws SQLException, FeatureStoreException, FilterEvaluationException {

        FeatureRow featureRow = null;
        try {
            featureRow = lookupFeatureRow( feature );

            // tracks all rows of this feature instance
            List<InsertRow> allRows = new ArrayList<InsertRow>();
            allRows.add( featureRow );

            for ( Mapping particleMapping : ftMapping.getMappings() ) {
                buildInsertRows( feature, particleMapping, featureRow, allRows );
            }

            LOG.debug( "Built rows for feature '" + feature.getId() + "': " + allRows.size() );

            for ( InsertRow insertRow : allRows ) {
                if ( !insertRow.hasParents() ) {
                    rootRows.add( insertRow );
                }
            }

            LOG.debug( "Before heap run: uninserted rows: " + delayedRows.size() + ", root rows: " + rootRows.size() );
            processHeap();
            LOG.debug( "After heap run: uninserted rows: " + delayedRows.size() + ", root rows: " + rootRows.size() );

        } catch ( Throwable t ) {
            LOG.debug( t.getMessage(), t );
            throw new FeatureStoreException( t.getMessage(), t );
        }
        return featureRow;
    }

    public FeatureRow updateFeature( final Feature feature, final FeatureTypeMapping ftMapping, final String[] idParts,
                                     Mapping mapping, ParsedPropertyReplacement replacement )
                            throws SQLException, FeatureStoreException, FilterEvaluationException {

        FeatureRow featureRow = null;
        try {
            featureRow = new FeatureRow( this, feature.getId(), tablename ) {
                @Override
                void performInsert( Connection conn, boolean propagateAutoGenColumns )
                                        throws SQLException, FeatureStoreException {
                    // don't
                }

                @Override
                public Object get( SQLIdentifier id ) {
                    int idx = 0;
                    for ( Pair<SQLIdentifier, BaseType> p : ftMapping.getFidMapping().getColumns() ) {
                        if ( p.first.equals( id ) ) {
                            // TODO need to use something other than string here?
                            return idParts[idx];
                        }
                        ++idx;
                    }
                    return null;
                }
            };

            // tracks all rows of this feature instance
            List<InsertRow> allRows = new ArrayList<InsertRow>();
            allRows.add( featureRow );

            buildInsertRows( feature, mapping, featureRow, allRows );

            LOG.debug( "Built rows for feature '" + feature.getId() + "': " + allRows.size() );

            for ( InsertRow insertRow : allRows ) {
                if ( !insertRow.hasParents() ) {
                    rootRows.add( insertRow );
                }
            }

            LOG.debug( "Before heap run: uninserted rows: " + delayedRows.size() + ", root rows: " + rootRows.size() );
            processHeap();
            LOG.debug( "After heap run: uninserted rows: " + delayedRows.size() + ", root rows: " + rootRows.size() );

        } catch ( Throwable t ) {
            LOG.debug( t.getMessage(), t );
            throw new FeatureStoreException( t.getMessage(), t );
        }
        return featureRow;
    }

    SQLDialect getDialect() {
        return dialect;
    }

    Connection getConnection() {
        return conn;
    }

    IDGenMode getIdGenMode() {
        return idGenMode;
    }

    MappedAppSchema getSchema() {
        return mappedschema;
    }

    Set<SQLIdentifier> getGenColumns( TableName table ) {
        return tableDeps.getGeneratedColumns( table );
    }

    Set<SQLIdentifier> getKeyColumns( TableName table ) {
        return tableDeps.getKeyColumns( table );
    }

    private FeatureRow lookupFeatureRow( String fid )
                            throws FeatureStoreException {
        FeatureRow featureRow = origFidToFeatureRow.get( fid );
        if ( featureRow == null ) {
            featureRow = new FeatureRow( this, fid, tablename );
            origFidToFeatureRow.put( fid, featureRow );
            delayedRows.add( featureRow );
        }
        return featureRow;
    }

    private FeatureRow lookupFeatureRow( Feature feature )
                            throws FeatureStoreException {
        FeatureRow featureRow = origFidToFeatureRow.get( feature.getId() );
        if ( featureRow == null ) {
            featureRow = new FeatureRow( this, feature.getId(), tablename );
            delayedRows.add( featureRow );
            if ( feature.getId() != null ) {
                origFidToFeatureRow.put( feature.getId(), featureRow );
            }
        }

        if ( !featureRow.isAssigned() ) {
            featureRow.assign( feature );
        }

        return featureRow;
    }

    public void buildInsertRows( final TypedObjectNode particle, final Mapping mapping, final InsertRow row,
                                 List<InsertRow> additionalRows )
                            throws FilterEvaluationException, FeatureStoreException {

        List<TableJoin> jc = mapping.getJoinedTable();
        if ( jc != null ) {
            if ( jc.size() != 1 ) {
                throw new FeatureStoreException( "Handling of joins with " + jc.size() + " steps is not implemented." );
            }
        }

        TypedObjectNodeXPathEvaluator evaluator = new TypedObjectNodeXPathEvaluator();
        TypedObjectNode[] values = evaluator.eval( particle, mapping.getPath() );
        int childIdx = 1;
        for ( TypedObjectNode value : values ) {
            InsertRow currentRow = row;
            if ( jc != null && !( mapping instanceof FeatureMapping ) ) {
                TableJoin join = jc.get( 0 );
                currentRow = buildJoinRow( currentRow, join );
                additionalRows.add( currentRow );
            }
            if ( mapping instanceof PrimitiveMapping ) {
                MappingExpression me = ( (PrimitiveMapping) mapping ).getMapping();
                if ( !( me instanceof DBField ) ) {
                    LOG.debug( "Skipping primitive mapping. Not mapped to database column." );
                } else {
                    @SuppressWarnings("unchecked")
                    ParticleConverter<PrimitiveValue> converter = (ParticleConverter<PrimitiveValue>) getConverter( mapping );
                    PrimitiveValue primitiveValue = getPrimitiveValue( value );
                    if ( primitiveValue != null ) {
                        String column = ( (DBField) me ).getColumn();
                        currentRow.addPreparedArgument( column, primitiveValue, converter );
                    }
                }
            } else if ( mapping instanceof GeometryMapping ) {
                MappingExpression me = ( (GeometryMapping) mapping ).getMapping();
                if ( !( me instanceof DBField ) ) {
                    LOG.debug( "Skipping geometry mapping. Not mapped to database column." );
                } else {
                    Geometry geom = (Geometry) getPropValue( value );
                    @SuppressWarnings("unchecked")
                    ParticleConverter<Geometry> converter = (ParticleConverter<Geometry>) getConverter( mapping );
                    String column = ( (DBField) me ).getColumn();
                    currentRow.addPreparedArgument( column, geom, converter );
                }
            } else if ( mapping instanceof FeatureMapping ) {
                FeatureRow subFeatureRow = null;
                String href = null;
                Feature feature = (Feature) getPropValue( value );
                if ( feature instanceof FeatureReference ) {
                    if ( ( (FeatureReference) feature ).isLocal() || ( (FeatureReference) feature ).isResolved() ) {
                        subFeatureRow = lookupFeatureRow( feature.getId() );
                    }
                    // always use the uri if href is mapped explicitly
                    href = ( (FeatureReference) feature ).getURI();
                    MappingExpression me = ( (FeatureMapping) mapping ).getHrefMapping();
                    if ( !( me instanceof DBField ) ) {
                        LOG.debug( "Skipping feature mapping (href). Not mapped to database column." );
                    } else {
                        String column = ( (DBField) me ).getColumn();
                        row.addPreparedArgument( column, href );
                    }
                } else if ( feature != null ) {
                    subFeatureRow = lookupFeatureRow( feature );
                }

                if ( subFeatureRow != null ) {

                    // TODO: pure href propagation (no fk)

                    if ( jc == null || jc.isEmpty() ) {
                        LOG.debug( "Skipping feature mapping (fk). Not mapped to database column." );
                    } else {
                        TableJoin join = jc.get( 0 );
                        KeyPropagation keyPropagation = getKeyPropagation( (FeatureMapping) mapping, join );
                        // standard: pk in subfeature table (usually feature id)
                        ParentRowReference ref = new ParentRowReference( subFeatureRow, keyPropagation );
                        currentRow.addParent( ref );
                        List<InsertRow> children = rowToChildRows.get( subFeatureRow );
                        if ( children == null ) {
                            children = new ArrayList<InsertRow>();
                            rowToChildRows.put( subFeatureRow, children );
                        }
                        children.add( currentRow );

                        SQLIdentifier hrefCol = null;
                        if ( ( (FeatureMapping) mapping ).getHrefMapping() != null ) {
                            hrefCol = new SQLIdentifier( ( (FeatureMapping) mapping ).getHrefMapping().toString() );
                        }
                        ref.addHrefingRow( currentRow, hrefCol );

                        if ( !delayedRows.contains( subFeatureRow ) ) {
                            // sub feature already inserted, propagate key values right away
                            currentRow.removeParent( subFeatureRow );
                        }
                    }
                }
            } else if ( mapping instanceof CompoundMapping ) {
                for ( Mapping child : ( (CompoundMapping) mapping ).getParticles() ) {
                    buildInsertRows( value, child, currentRow, additionalRows );
                }
            } else if ( mapping instanceof ConstantMapping ) {
                // nothing to do
            } else {
                LOG.warn( "Unhandled mapping type '" + mapping.getClass() + "'." );
            }

            // add index column value if the join uses a numbered order column
            if ( jc != null && jc.size() == 1 ) {
                TableJoin join = jc.get( 0 );
                if ( join.isNumberedOrder() ) {
                    for ( SQLIdentifier col : join.getOrderColumns() ) {
                        if ( currentRow.get( col ) == null ) {
                            // TODO do this properly
                            currentRow.addLiteralValue( col, "" + childIdx++ );
                        }
                    }
                }
            }
        }
    }

    // special handling for joins to feature type tables
    private KeyPropagation getKeyPropagation( FeatureMapping mapping, TableJoin join )
                            throws FeatureStoreException {

        SQLIdentifier fromColumn = join.getFromColumns().get( 0 );
        SQLIdentifier toColumn = join.getToColumns().get( 0 );

        TableName ftTable = null;
        // a bit dirty: if no feature type is specified, use any
        QName ftName = getSchema().getFtMappings().keySet().iterator().next();
        if ( mapping.getValueFtName() != null ) {
            ftName = mapping.getValueFtName();
            if ( getSchema().getFeatureType( ftName ).isAbstract() ) {
                // may be abstract, so take any concrete substitution feature type
                FeatureType[] concreteSubtypes = getSchema().getConcreteSubtypes( getSchema().getFeatureType( ftName ) );
                if ( concreteSubtypes.length == 0 ) {
                    String msg = "Error in mapping. Feature-particle mapping " + mapping
                                 + " has an abstract value feature type ('" + ftName
                                 + "') with no concrete substitutions.";
                    throw new FeatureStoreException( msg );
                }
                ftName = getSchema().getConcreteSubtypes( getSchema().getFeatureType( ftName ) )[0].getName();
            }
            FeatureTypeMapping ftMapping = getSchema().getFtMapping( ftName );
            ftTable = ftMapping.getFtTable();
        } else if ( !join.getToTable().getName().equals( "?" ) ) {
            // I hope this does not break anything. Use the table configured in the Join mapping if the schema did not
            // reveal the value feature type
            ftTable = join.getToTable();
        }
        Set<SQLIdentifier> ftTableGenColumns = tableDeps.getKeyColumns( ftTable );
        if ( ftTableGenColumns != null && ftTableGenColumns.contains( toColumn ) ) {
            List<SQLIdentifier> toColumns = Collections.singletonList( toColumn );
            List<SQLIdentifier> fromColumns = Collections.singletonList( fromColumn );
            return new KeyPropagation( ftTable, toColumns, join.getFromTable(), fromColumns );
        }

        // must be the other way round
        String msg = "Propagating feature property fks from join tables into target feature tables is not supported yet.";
        throw new UnsupportedOperationException( msg );
    }

    private JoinRow buildJoinRow( InsertRow row, TableJoin join )
                            throws FeatureStoreException {

        JoinRow newRow = new JoinRow( this, join, tablename );
        delayedRows.add( newRow );

        KeyPropagation keyPropagation = tableDeps.findKeyPropagation( join.getFromTable(), join.getFromColumns(),
                                                                      join.getToTable(), join.getToColumns() );
        if ( keyPropagation == null ) {
            String msg = "Internal error: table dependencies don't contain join " + join;
            throw new FeatureStoreException( msg );
        }

        if ( keyPropagation.getSourceTable().equals( join.getFromTable() ) ) {
            ParentRowReference ref = new ParentRowReference( row, keyPropagation );
            newRow.addParent( ref );
            List<InsertRow> children = rowToChildRows.get( row );
            if ( children == null ) {
                children = new ArrayList<InsertRow>();
                rowToChildRows.put( row, children );
            }
            children.add( newRow );
        } else {
            ParentRowReference ref = new ParentRowReference( newRow, keyPropagation );
            row.addParent( ref );
            List<InsertRow> children = new ArrayList<InsertRow>();
            rowToChildRows.put( newRow, children );
            children.add( row );
        }

        return newRow;
    }

    private PrimitiveValue getPrimitiveValue( TypedObjectNode value ) {
        if ( value instanceof Property ) {
            value = ( (Property) value ).getValue();
        }
        if ( value instanceof GenericXMLElement ) {
            value = ( (GenericXMLElement) value ).getValue();
        }
        return (PrimitiveValue) value;
    }

    private TypedObjectNode getPropValue( TypedObjectNode prop ) {
        if ( prop instanceof Property ) {
            return ( (Property) prop ).getValue();
        }
        return prop;
    }

    public void processHeap()
                            throws SQLException, FeatureStoreException {

        while ( !rootRows.isEmpty() ) {
            List<InsertRow> rootRemoves = new ArrayList<InsertRow>();
            List<InsertRow> rootAdds = new ArrayList<InsertRow>();
            for ( InsertRow row : rootRows ) {
                LOG.debug( "Inserting row " + row );
                row.performInsert( conn, rowToChildRows.get( row ) != null );
                delayedRows.remove( row );
                rootRemoves.add( row );

                // update child rows
                List<InsertRow> childRows = rowToChildRows.get( row );
                if ( childRows != null ) {
                    for ( InsertRow childRow : childRows ) {
                        LOG.debug( "Child row: " + childRow );
                        childRow.removeParent( row );
                        if ( !childRow.hasParents() ) {
                            rootAdds.add( childRow );
                        }
                    }
                    rowToChildRows.remove( row );
                }
            }
            rootRows.removeAll( rootRemoves );
            rootRows.addAll( rootAdds );
        }
    }

    /**
     * Returns the number of currently delayed rows (rows that depend on some other row to be inserted first).
     * 
     * @return number of currently delayed rows
     */
    public int getDelayedRows() {
        return delayedRows.size();
    }
    
    
    private void initConverters() {
        for ( FeatureType ft : mappedschema.getFeatureTypes() ) {
            FeatureTypeMapping ftMapping = mappedschema.getFtMapping( ft.getName() );
            if ( ftMapping != null ) {
                for ( Mapping particleMapping : ftMapping.getMappings() ) {
                    initConverter( particleMapping );
                }
            }
        }
    }

    @SuppressWarnings("unchecked")
	private void initConverter( Mapping particleMapping ) {
        if ( particleMapping instanceof PrimitiveMapping ) {
        	System.out.println("Primitive mapping");
            PrimitiveMapping pm = (PrimitiveMapping) particleMapping;
            ParticleConverter<?> converter = null;
            if ( pm.getConverter() == null ) {
                converter = dialect.getPrimitiveConverter( pm.getMapping().toString(), pm.getType() );
            } else {
            	System.out.println("ELSE");
                converter = instantiateConverter( pm.getConverter() );
                ( (CustomParticleConverter<TypedObjectNode>) converter ).init( particleMapping, null );
            }
            particleMappingToConverter.put( particleMapping, converter );
        } else if ( particleMapping instanceof GeometryMapping ) {
        	System.out.println("Geometry mapping");
            GeometryMapping gm = (GeometryMapping) particleMapping;
            ParticleConverter<?> converter = getGeometryConverter( gm );
            particleMappingToConverter.put( particleMapping, converter );
        } else if ( particleMapping instanceof FeatureMapping ) {
        	System.out.println("Feature mapping");
            FeatureMapping fm = (FeatureMapping) particleMapping;
            SQLIdentifier fkColumn = null;
            if ( fm.getJoinedTable() != null && !fm.getJoinedTable().isEmpty() ) {
                // TODO more complex joins
                fkColumn = fm.getJoinedTable().get( fm.getJoinedTable().size() - 1 ).getFromColumns().get( 0 );
            }
            SQLIdentifier hrefColumn = null;
            if ( fm.getHrefMapping() != null ) {
                hrefColumn = new SQLIdentifier( fm.getHrefMapping().toString() );
            }
            FeatureType valueFt = null;
            if ( fm.getValueFtName() != null ) {
                valueFt = mappedschema.getFeatureType( fm.getValueFtName() );
            }
            ParticleConverter<?> converter = new FeatureParticleConverter( fkColumn, hrefColumn, getResolver(),
                                                                           valueFt, mappedschema );
            particleMappingToConverter.put( particleMapping, converter );
        } else if ( particleMapping instanceof CompoundMapping ) {
        	System.out.println("Compound mapping");
            CompoundMapping cm = (CompoundMapping) particleMapping;
            for ( Mapping childMapping : cm.getParticles() ) {
                initConverter( childMapping );
            }
        } else {
            LOG.warn( "Unhandled particle mapping type {}", particleMapping );
        }
    }

    public ParticleConverter<?> getConverter( Mapping mapping ) {
        return particleMappingToConverter.get( mapping );
    }
    
    @SuppressWarnings("unchecked")
    private CustomParticleConverter<TypedObjectNode> instantiateConverter( CustomConverterJAXB config ) {
        String className = config.getClazz();
        LOG.info( "Instantiating configured custom particle converter (class=" + className + ")" );
        try {
            //return (CustomParticleConverter<TypedObjectNode>) workspace.getModuleClassLoader().loadClass( className ).newInstance();
        	return null;
        } catch ( Throwable t ) {
            String msg = "Unable to instantiate custom particle converter (class=" + className + "). "
                         + " Maybe directory 'modules' in your workspace is missing the JAR with the "
                         + " referenced converter class?! " + t.getMessage();
            LOG.error( msg, t );
            throw new IllegalArgumentException( msg );
        }
    }
    
    ParticleConverter<Geometry> getGeometryConverter( GeometryMapping geomMapping ) {
        String column = geomMapping.getMapping().toString();
        ICRS crs = geomMapping.getCRS();
        String srid = geomMapping.getSrid();
        boolean is2d = geomMapping.getDim() == CoordinateDimension.DIM_2;
        return dialect.getGeometryConverter( column, crs, srid, is2d );
    }
    
    public GMLReferenceResolver getResolver() {
        return resolver;
    }
    /**
     * Code from  SQLFeatureStoreTransaction.ImportData:
     * @param fCollection FeatureCollection of the GML file to import
     * @throws FeatureStoreException
     * @throws SQLException
     * @throws FilterEvaluationException
     */
    public void importData(FeatureCollection fCollection) throws FeatureStoreException, SQLException, FilterEvaluationException {
    	
    	List<FeatureRow> idAssignments = new ArrayList<FeatureRow>();
		BBoxTracker bboxTracker = new BBoxTracker();

		Set<Geometry> geometries = new LinkedHashSet<Geometry>();
		Set<Feature> features = new LinkedHashSet<Feature>();
		Set<String> fids = new LinkedHashSet<String>();
		Set<String> gids = new LinkedHashSet<String>();

		for (Feature member : fCollection) {
			findFeaturesAndGeometries(member, geometries, features, fids, gids);
		}

		for (Feature feature : features) {
			FeatureTypeMapping ftMapping = mappedschema.getFtMapping(feature
					.getName());
			if (ftMapping == null) {
				throw new FeatureStoreException(
						"Cannot insert feature of type '" + feature.getName()
								+ "'. No mapping defined and BLOB mode is off.");
			}
			idAssignments.add(insertFeature(feature, ftMapping));
			Pair<TableName, GeometryMapping> mapping = ftMapping
					.getDefaultGeometryMapping();
			if (mapping != null) {
				ICRS storageSrs = mapping.second.getCRS();
				bboxTracker.insert(feature, storageSrs);
			}
		}
		if (getDelayedRows() != 0) {
			String msg = "After insertion, "
					+ getDelayedRows()
					+ " delayed rows left uninserted. Probably a cyclic key constraint blocks insertion.";
			throw new RuntimeException(msg);
		}
		// TODO why is this necessary?
		fids.clear();
		for (FeatureRow assignment : idAssignments) {
			fids.add(assignment.getNewId());
		}

    	
    }
}
