(function (root, factory) {
  'use strict';
  const presentation = factory();
  if (typeof module === 'object' && module.exports) module.exports = presentation;
  if (root) root.MSCGraphPresentation = presentation;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  // Editorial navigation colors, NOT an additional official MSC hierarchy.
  // Every official top-level code is assigned once. Broad subjects can have
  // several mathematical interpretations; colors do not assert equivalence.
  const groups = [
    {id:'foundations', shortLabel:'Основы', label:'Основы, история и образование', color:'#64748b', roots:['00','01','03','97']},
    {id:'discrete', shortLabel:'Дискретная', label:'Дискретная математика', color:'#c38b22', roots:['05','06']},
    {id:'algebra', shortLabel:'Алгебра', label:'Алгебра и числа', color:'#6559c5', roots:['08','11','12','13','15','16','17','18','19','20','22']},
    {id:'geometry', shortLabel:'Геометрия', label:'Геометрия и топология', color:'#168b82', roots:['14','51','52','53','54','55','57','58']},
    {id:'analysis', shortLabel:'Анализ', label:'Анализ', color:'#3478bd', roots:['26','28','30','31','32','33','34','35','37','39','40','41','42','43','44','45','46','47','49']},
    {id:'probability', shortLabel:'Вероятность', label:'Вероятность и статистика', color:'#b75589', roots:['60','62']},
    {id:'computation', shortLabel:'Вычисления', label:'Вычисления и информация', color:'#258ca7', roots:['65','68','94']},
    {id:'physics', shortLabel:'Физика', label:'Математическая физика', color:'#c66c42', roots:['70','74','76','78','80','81','82','83','85','86']},
    {id:'models', shortLabel:'Модели', label:'Модели и управление', color:'#6d8b44', roots:['90','91','92','93']}
  ];
  const byRoot = new Map();
  for (const group of groups) {
    Object.freeze(group.roots);
    Object.freeze(group);
    for (const root of group.roots) {
      if (byRoot.has(root)) throw new TypeError('Duplicate color assignment: ' + root);
      byRoot.set(root, group);
    }
  }
  Object.freeze(groups);

  function groupForRoot(root) { return byRoot.get(root) || null; }

  function decorate(graph) {
    if (!graph || !Array.isArray(graph.nodes) || !Array.isArray(graph.edges)) {
      throw new TypeError('A graph with node and edge arrays is required.');
    }
    return {
      ...graph,
      nodes: graph.nodes.map(node => {
        const group = groupForRoot(node.data.root);
        return {...node, data:{...node.data,
          color: group ? group.color : '#64748b',
          colorGroup: group ? group.id : 'context',
          colorGroupLabel: group ? group.label : 'Навигационный контекст'
        }};
      }),
      edges: graph.edges.map(edge => ({...edge, data:{...edge.data}}))
    };
  }

  return Object.freeze({groups, groupForRoot, decorate,
    description:'Цветовые группы для навигации. Это редакционное объединение областей, не дополнительный уровень MSC и не математическая эквивалентность.'});
});
