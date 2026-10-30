#!/usr/bin/env python3
"""Reproduce atlas analysis and verification without the browser."""
import argparse
import json
from pathlib import Path
import lean_service
from server import run_analysis,run_verification,RUNS

def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='command',required=True)
    demo=sub.add_parser('demo');demo.add_argument('example',nargs='?',default='astra-energy');demo.add_argument('--verify',action='store_true')
    analyze=sub.add_parser('analyze');analyze.add_argument('files',nargs=2,type=Path);analyze.add_argument('--project-root');analyze.add_argument('--lean');analyze.add_argument('--mathlib');analyze.add_argument('--targets',nargs=2,default=['',''])
    verify=sub.add_parser('verify');verify.add_argument('analysis_id');verify.add_argument('source',type=Path);verify.add_argument('--targets',nargs='+',required=True)
    args=p.parse_args()
    if args.command=='demo':
        example=next((e for e in lean_service.load_examples() if e['id']==args.example),None)
        if example is None: raise SystemExit('Unknown example: '+args.example)
        report=run_analysis(example)
        if args.verify:
            if not report.get('bridge_source'): raise SystemExit('Автоматический мост не предложен. Составьте Bridge.lean и используйте команду verify.')
            report['verification']=run_verification(dict(analysis_id=report['id'],bridge_source=report['bridge_source'],bridge_targets=report['bridge_targets']))
    elif args.command=='analyze':
        report=run_analysis(dict(files=[dict(name=f.name,content=f.read_text()) for f in args.files],context={k:getattr(args,k) for k in ['project_root','lean','mathlib'] if getattr(args,k)},targets=args.targets))
    else: report=run_verification(dict(analysis_id=args.analysis_id,bridge_source=args.source.read_text(),bridge_targets=args.targets))
    print(json.dumps(report,ensure_ascii=False,indent=2,default=str))
    if args.command=='verify' or (args.command=='demo' and args.verify):
        verification=report.get('verification',report)
        return 0 if verification.get('success') else 1
    return 0

if __name__=='__main__': raise SystemExit(main())
