import cytoscape from 'cytoscape';
import fcose from 'cytoscape-fcose';
import dagre from 'cytoscape-dagre';
cytoscape.use(fcose);
cytoscape.use(dagre);
globalThis.cytoscape = cytoscape;
