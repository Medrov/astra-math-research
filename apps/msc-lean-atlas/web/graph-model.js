(function (root, factory) {
  'use strict';
  const Model = factory();
  if (typeof module === 'object' && module.exports) module.exports = Model;
  if (root) root.MSCGraphModel = Model;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  const OVERVIEW_ID = '__msc__';
  const MODES = new Set(['overview', 'focus', 'local', 'full']);

  /** Selects source-backed MSC subgraphs without changing their edge semantics. */
  class MSCGraphModel {
    constructor(dataset) {
      if (!dataset || !Array.isArray(dataset.nodes) || !Array.isArray(dataset.edges)) {
        throw new TypeError('MSC dataset must contain nodes and edges arrays.');
      }
      this.dataset = dataset;
      this.nodeMap = new Map();
      this.children = new Map([[OVERVIEW_ID, []]]);
      this._rootCache = new Map([[OVERVIEW_ID, OVERVIEW_ID]]);

      for (const node of dataset.nodes) {
        if (!node || typeof node.id !== 'string' || !node.id || node.id === OVERVIEW_ID || this.nodeMap.has(node.id)) {
          throw new TypeError('MSC node IDs must be unique, nonempty strings; __msc__ is reserved.');
        }
        this.nodeMap.set(node.id, node);
        this.children.set(node.id, []);
      }
      for (const node of dataset.nodes) {
        const parent = node.parent_id == null ? OVERVIEW_ID : node.parent_id;
        if (!this.children.has(parent)) throw new TypeError('Unknown MSC parent: ' + parent);
        this.children.get(parent).push(node.id);
      }
      // Resolve once, detecting a corrupt hierarchy rather than making up parents.
      for (const node of dataset.nodes) this.rootOf(node.id);

      const elementIds = new Set([OVERVIEW_ID, ...this.nodeMap.keys()]);
      for (const edge of dataset.edges) {
        if (!edge || typeof edge.id !== 'string' || !edge.id || elementIds.has(edge.id)) {
          throw new TypeError('MSC edge IDs must be unique and distinct from node IDs.');
        }
        if (!this.nodeMap.has(edge.source) || !this.nodeMap.has(edge.target)) {
          throw new TypeError('MSC edge has an unknown endpoint: ' + edge.id);
        }
        elementIds.add(edge.id);
      }
      for (const root of this.children.get(OVERVIEW_ID)) {
        if (elementIds.has(this._overviewEdgeId(root))) throw new TypeError('Reserved overview edge ID collision.');
      }
    }

    rootOf(id) {
      if (this._rootCache.has(id)) return this._rootCache.get(id);
      if (!this.nodeMap.has(id)) return null;
      const path = [], visited = new Set();
      let current = id;
      while (!this._rootCache.has(current)) {
        if (visited.has(current)) throw new TypeError('Cyclic MSC hierarchy at ' + current);
        visited.add(current);
        path.push(current);
        const node = this.nodeMap.get(current);
        if (node.parent_id == null) {
          this._rootCache.set(current, current);
          break;
        }
        current = node.parent_id;
      }
      const root = this._rootCache.get(current);
      for (const item of path) this._rootCache.set(item, root);
      return root;
    }

    /** Source-order depth-first traversal, including the requested node itself. */
    descendants(id) {
      if (id !== OVERVIEW_ID && !this.nodeMap.has(id)) return [];
      const result = [], stack = [id];
      while (stack.length) {
        const current = stack.pop();
        result.push(current);
        const children = this.children.get(current) || [];
        for (let index = children.length - 1; index >= 0; index--) stack.push(children[index]);
      }
      return result;
    }

    _overviewEdgeId(root) { return 'overview:' + root + ':' + OVERVIEW_ID; }

    _nodeElement(node) {
      return {
        group: 'nodes',
        data: {
          id: node.id,
          code: node.code,
          title: node.title,
          level: node.level,
          mscParent: node.parent_id == null ? null : node.parent_id,
          root: this.rootOf(node.id),
          size: node.level === 0 ? 22 : node.level === 1 ? 13 : 7
        }
      };
    }

    elements({mode = 'overview', focusId = OVERVIEW_ID, references = false, depth = 1} = {}) {
      if (!MODES.has(mode)) throw new TypeError('Unknown MSC graph mode: ' + mode);
      if (focusId !== OVERVIEW_ID && !this.nodeMap.has(focusId)) {
        throw new TypeError('Unknown MSC focus: ' + focusId);
      }
      if (mode === 'local' && focusId === OVERVIEW_ID) {
        throw new TypeError('Local graph requires an actual MSC category, not the virtual overview.');
      }
      if (mode === 'local' && (!Number.isInteger(depth) || depth < 1 || depth > 3)) {
        throw new TypeError('Local graph depth must be an integer from 1 to 3.');
      }
      const visible = new Set(mode === 'local' ? [focusId] : [OVERVIEW_ID]);
      if (mode === 'full') {
        for (const node of this.dataset.nodes) visible.add(node.id);
      } else if (mode === 'overview') {
        for (const node of this.dataset.nodes) if (node.level <= 1) visible.add(node.id);
      } else if (mode === 'local') {
        // Locality is measured only over real source edges. Connecting every
        // root through the virtual center would create false two-hop neighbors.
        const adjacency = new Map();
        const connect = (from, to) => {
          if (!adjacency.has(from)) adjacency.set(from, []);
          adjacency.get(from).push(to);
        };
        for (const edge of this.dataset.edges) {
          if (!references && edge.type !== 'broader') continue;
          connect(edge.source, edge.target);
          connect(edge.target, edge.source);
        }
        let frontier = new Set([focusId]);
        for (let hop = 0; hop < depth && frontier.size; hop++) {
          const next = new Set();
          for (const id of frontier) {
            for (const neighbor of adjacency.get(id) || []) {
              if (!visible.has(neighbor)) {
                visible.add(neighbor);
                next.add(neighbor);
              }
            }
          }
          frontier = next;
        }
      } else {
        const selected = this.nodeMap.get(focusId);
        // A terminal category gets the context of its parent and siblings.
        const anchor = selected && !this.children.get(focusId).length && selected.parent_id != null
          ? selected.parent_id : focusId;
        const core = new Set(this.descendants(anchor));
        for (const id of core) visible.add(id);
        let ancestor = this.nodeMap.get(anchor);
        while (ancestor && ancestor.parent_id != null) {
          visible.add(ancestor.parent_id);
          ancestor = this.nodeMap.get(ancestor.parent_id);
        }
        if (references) {
          // Expand exactly one reference hop from the core, never recursively
          // from newly added endpoints or from broad ancestor context.
          for (const edge of this.dataset.edges) {
            if (edge.type !== 'broader' && (core.has(edge.source) || core.has(edge.target))) {
              visible.add(edge.source);
              visible.add(edge.target);
            }
          }
        }
      }

      const nodes = mode === 'local' ? [] : [{
        group: 'nodes',
        data: {id: OVERVIEW_ID, code: 'MSC2020', title: 'MSC2020', level: -1, mscParent: null, root: OVERVIEW_ID, size: 36}
      }];
      for (const node of this.dataset.nodes) if (visible.has(node.id)) nodes.push(this._nodeElement(node));

      const edges = [];
      let referenceCount = 0;
      for (const edge of this.dataset.edges) {
        if (!visible.has(edge.source) || !visible.has(edge.target) || (!references && edge.type !== 'broader')) continue;
        edges.push({group: 'edges', data: {...edge, reference_text: edge.reference_text || ''}});
        if (edge.type !== 'broader') referenceCount++;
      }
      // These edges exist only in the viewer. They never pretend to be source
      // hierarchy or mathematical connections and are not added to the dataset.
      for (const root of this.children.get(OVERVIEW_ID)) {
        if (visible.has(OVERVIEW_ID) && visible.has(root)) edges.push({
          group: 'edges',
          data: {id: this._overviewEdgeId(root), source: root, target: OVERVIEW_ID, type: 'overview', reference_text: ''}
        });
      }
      return {nodes, edges, focusId, mode, depth: mode === 'local' ? depth : undefined,
        realNodeCount: nodes.filter(node => node.data.id !== OVERVIEW_ID).length, referenceCount};
    }
  }

  return MSCGraphModel;
});
