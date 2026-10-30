/* fCoSE runs off the browser UI thread. Uploaded Lean sources never enter this worker. */
importScripts('/vendor/graph-libs.min.js');
self.onmessage = ({data}) => {
  let cy;
  try {
    cy=cytoscape({headless:true,styleEnabled:true,elements:data.elements,
      // Reserve room for the code below each circular node in the force layout.
      style:[{selector:'node',style:{width:n=>Math.max(n.data('size'),n.data('code').length*9),height:n=>Math.max(n.data('size'),18)+18}}]});
    cy.layout({name:'fcose',quality:'default',randomize:true,animate:false,fit:false,packComponents:false,
      nodeDimensionsIncludeLabels:false,nodeRepulsion:()=>9000,
      idealEdgeLength:e=>e.data('type')==='overview'?140:e.source().data('level')<2?100:58,
      edgeElasticity:()=>0.45,numIter:1400,gravity:0.12,tiling:true}).run();
    const positions={};cy.nodes().forEach(n=>{const {x,y}=n.position();if(!Number.isFinite(x)||!Number.isFinite(y))throw Error('Некорректные координаты узла '+n.id());positions[n.id()]={x,y};});
    self.postMessage({positions});
  } catch(error){self.postMessage({error:error.message});}
  finally{cy?.destroy();}
};
