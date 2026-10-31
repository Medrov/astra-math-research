/* Domain colours come only from the shared MSC navigation palette. */
(function(root,factory){const api=factory(root);if(typeof module==='object'&&module.exports)module.exports=api;else root.ResearchAppearance=api;})(typeof globalThis==='undefined'?this:globalThis,function(root){
  'use strict';
  const list=value=>Array.isArray(value)?value:[],neutral='#64748b',white='#ffffff',ink='#243247';
  const rgb=hex=>/^#[0-9a-f]{6}$/i.test(hex||'')?[1,3,5].map(start=>parseInt(hex.slice(start,start+2),16)):null;
  const hex=channels=>'#'+channels.map(value=>Math.max(0,Math.min(255,Math.round(value))).toString(16).padStart(2,'0')).join('');
  function mix(color,other,amount){const a=rgb(color)||rgb(neutral),b=rgb(other)||rgb(white);return hex(a.map((value,index)=>value*(1-amount)+b[index]*amount));}
  function luminance(color){const channels=rgb(color);if(!channels)return null;return channels.map(value=>{const v=value/255;return v<=.04045?v/12.92:((v+.055)/1.055)**2.4;}).reduce((sum,value,index)=>sum+value*[.2126,.7152,.0722][index],0);}
  function contrast(a,b){const x=luminance(a),y=luminance(b);return x===null||y===null?0:(Math.max(x,y)+.05)/(Math.min(x,y)+.05);}
  function solid(color,background=white){let value=rgb(color)?color:neutral;while(contrast(value,background)<4.6)value=mix(value,'#000000',.04);return value;}
  function familyFor(item,presentation=root.MSCGraphPresentation){
    if(item?.known!==true||!list(item.path).length||typeof presentation?.groupForRoot!=='function')return null;
    const group=presentation.groupForRoot(item.path[0]?.code);
    return group&&rgb(group.color)?{id:group.id,label:group.label,shortLabel:group.shortLabel||group.label,color:group.color}:null;
  }
  function forMSC(item,presentation=root.MSCGraphPresentation){const family=familyFor(item,presentation),color=family?.color||neutral,fill=mix(color,white,.92);return {family,fill,border:mix(color,white,.58),text:solid(color,fill)};}
  function forNode(node,context,presentation=root.MSCGraphPresentation){
    const items=list(context?.items),mapped=items.map(item=>familyFor(item,presentation)),families=[...new Map(mapped.filter(Boolean).map(family=>[family.id,family])).values()];
    const contextual=!['explicit','route','related_objects','selected_transition'].includes(context?.origin);
    let classification,label,color=neutral;
    if(contextual){classification=context?.origin==='research'?'context':'unknown';label=context?.origin==='research'?'Контекст исследования':'Область не указана';}
    else if(families.length>1){classification='mixed';label='Несколько областей';}
    else if(families.length===1&&mapped.every(Boolean)){classification='family';label=families[0].label;color=families[0].color;}
    else if(families.length===1){classification='partial';label='Область определена частично';}
    else{classification='unknown';label='Область не определена';}
    const transition=node?.kind==='transition',fill=transition?solid(color):mix(color,white,.88);
    return {classification,label,families:contextual?[]:families,fill,border:transition?solid(color):mix(color,white,.25),text:transition?white:ink,shape:transition?'round-hexagon':'round-rectangle',tint:mix(color,white,.96)};
  }
  return {forNode,forMSC,contrast};
});
