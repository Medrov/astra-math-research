/* Reproducible local browser bundle and offline fCoSE layout. No CDN at runtime. */
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const cytoscape = require('cytoscape');
cytoscape.use(require('cytoscape-fcose'));
const root = path.resolve(__dirname, '..');
const MSCGraphModel = require('../web/graph-model.js');

(async () => {
  const vendor = path.join(root, 'web/vendor');
  fs.mkdirSync(vendor, {recursive: true});
  await require('esbuild').build({entryPoints:[path.join(__dirname,'graph-libs-entry.js')], bundle:true, minify:true,
    format:'iife', platform:'browser', target:['es2020'], outfile:path.join(vendor,'graph-libs.min.js'), legalComments:'eof'});
  const packages=['cytoscape','cytoscape-fcose','cose-base','layout-base','cytoscape-dagre'];
  const versions=Object.fromEntries(packages.map(name=>[name,JSON.parse(fs.readFileSync(path.join(root,'node_modules',name,'package.json'))).version]));
  const licenses=packages.map(name=>`${name} ${versions[name]}\nhttps://www.npmjs.com/package/${name}\n\n${fs.readFileSync(path.join(root,'node_modules',name,'LICENSE'),'utf8')}`).join('\n\n'+ '='.repeat(72)+'\n\n');
  fs.writeFileSync(path.join(vendor,'LICENSES.txt'),licenses+'\n\n'+fs.readFileSync(path.join(__dirname,'DAGRE_LICENSE.txt'),'utf8'));
  const manifest={versions,bundle_sha256:crypto.createHash('sha256').update(fs.readFileSync(path.join(vendor,'graph-libs.min.js'))).digest('hex'),layout_file:'../graph-layouts.json',license:'MIT'};
  fs.writeFileSync(path.join(vendor,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');
  if(process.argv.includes('--bundle-only')){console.log('Graph bundle updated; existing MSC coordinates preserved.');return;}
  const raw=fs.readFileSync(path.join(root,'data/msc2020.json'));
  const dataset=JSON.parse(raw),model=new MSCGraphModel(dataset);
  const result={meta:{algorithm:'fCoSE',versions,dataset_sha256:crypto.createHash('sha256').update(raw).digest('hex'),source_sha256:dataset.meta.source_sha256,node_count:dataset.nodes.length,created_at:new Date().toISOString(),layout_edges:'hierarchy and explicitly virtual overview links; references do not attract nodes'},layouts:{}};
  // Seed the layout library's random sampling so a rebuild is reproducible.
  let seed=20201030;
  Math.random=()=>{seed=(Math.imul(1664525,seed)+1013904223)>>>0;return seed/4294967296;};
  for(const mode of ['overview','full']){
    const start=Date.now(),graph=model.elements({mode,references:false});
    const cy=cytoscape({headless:true,styleEnabled:true,elements:[...graph.nodes,...graph.edges],
      style:[{selector:'node',style:{width:'data(size)',height:'data(size)'}}]});
    console.log(`fCoSE ${mode}: ${graph.nodes.length} nodes, ${graph.edges.length} edges`);
    cy.layout({name:'fcose',quality:'default',randomize:true,animate:false,fit:false,packComponents:false,
      nodeDimensionsIncludeLabels:false,nodeRepulsion:()=>10000,
      idealEdgeLength:e=>e.data('type')==='overview'?300:e.source().data('level')===1?120:45,
      edgeElasticity:()=>0.45,numIter:2000,gravity:0.12,tiling:true}).run();
    const positions={};
    cy.nodes().forEach(node=>{const {x,y}=node.position();if(!Number.isFinite(x)||!Number.isFinite(y))throw Error('Invalid coordinate: '+node.id());positions[node.id()]={x:Math.round(x*100)/100,y:Math.round(y*100)/100};});
    result.layouts[mode]={positions,node_count:graph.nodes.length,edge_count:graph.edges.length,elapsed_ms:Date.now()-start};
    cy.destroy();console.log(`${mode} saved in ${result.layouts[mode].elapsed_ms} ms`);
  }
  fs.writeFileSync(path.join(root,'web/graph-layouts.json'),JSON.stringify(result));
  fs.writeFileSync(path.join(vendor,'manifest.json'),JSON.stringify({versions,bundle_sha256:crypto.createHash('sha256').update(fs.readFileSync(path.join(vendor,'graph-libs.min.js'))).digest('hex'),layout_file:'../graph-layouts.json',license:'MIT'},null,2)+'\n');
})().catch(error=>{console.error(error);process.exitCode=1;});
