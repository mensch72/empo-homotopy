import json,numpy as np
for m in ('lin','nonlin','traj'):
    R=json.load(open('out/results_%s.json'%m)); multi=[r for r in R if 'game' in r]
    fl=[min(r['folds']) for r in R if r['folds']]
    g=lambda r:[float(b) for b,n in r['n'].items() if n>=2]
    print(m,'N',len(R),'multi',len(multi),'ncv',sum(r['ncv'] for r in R),'vediag bad/n',sum(r['vediag_bad'] for r in R),sum(r['vediag_n'] for r in R),'rho_fail/nev',sum(r.get('rho_fail',0) for r in R),sum(r.get('nev',0) for r in R))
    print(' folds instances',len(fl),'min fold beta',round(min(fl),3) if fl else None,'| multi at grid beta<=1:',sum(1 for r in R if any(b<=1 for b in g(r))),'| min grid beta with mult',min([min(g(r)) for r in multi],default=None),'| max #sol',max(max(r['n'].values()) for r in R))
    print(' first-mult grid-beta histogram',{b:sum(1 for r in multi if min(g(r))==b) for b in sorted({min(g(r)) for r in multi})})
    print(' max rho_J per beta',[round(max(r['rho'][b] for r in R),2) for b in R[0]['rho']],' #(inst,beta) with 0 sols',sum(1 for r in R for n in r['n'].values() if n==0))
    print(' size of smallest multi',sorted((r['size'],r['dims'][:2]+r['dims'][2:],r['i']) for r in multi)[:3], 'kinds none')
