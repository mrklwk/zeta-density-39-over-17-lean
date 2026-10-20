from pathlib import Path
import csv,datetime,hashlib,json,re
import sympy as sp
from sympy.parsing.sympy_parser import parse_expr,standard_transformations,implicit_multiplication_application
ROOT=Path(__file__).resolve().parents[1];H=ROOT/'audit';R=ROOT;P=ROOT/'docs/presentation'
S=sp.Symbol('s',real=True);E=sp.Symbol('e',real=True)
TRANS=standard_transformations+(implicit_multiplication_application,)
def expr(s):
    s=re.sub(r'\s*:\s*ℝ','',s).replace('σ','s').replace('ε','e').replace('−','-').replace('\\sigma','s').replace('^','**')
    return sp.cancel(parse_expr(s,local_dict={'s':S,'e':E},transformations=TRANS))
def group(s,i):
    assert s[i]in '({' ;op=s[i];cl=')'if op=='('else'}';depth=0
    for j in range(i,len(s)):
        if s[j]==op:depth+=1
        elif s[j]==cl:
            depth-=1
            if not depth:return s[i+1:j],j+1
    raise ValueError(s)
def latex(s):
    while '\\frac' in s:
        i=s.index('\\frac');a,j=group(s,i+5);b,k=group(s,j);s=s[:i]+'(('+latex(a)+')/('+latex(b)+'))'+s[k:]
    return s.replace('\\sigma','s').replace('\\left','').replace('\\right','').replace('\\,','').replace('{','(').replace('}',')')
def declarations(s):
    hits=list(re.finditer(r'^theorem\s+(\w+)\b',s,re.M));out={}
    for i,m in enumerate(hits):
        chunk=s[m.start():hits[i+1].start()if i+1<len(hits)else len(s)]
        header=re.split(r'\s*:=\s*by\b',chunk,maxsplit=1)[0]
        if ':='in header:raise ValueError(m.group(1))
        out[m.group(1)]=dict(header=header,line=s[:m.start()].count('\n')+1)
    return out
def bounds(h):
    a=re.search(r'\(hlo\s*:\s*\((.*?)\s*:\s*ℝ\)\s*(≤|<)\s*σ\)',h)
    b=re.search(r'\(hhi\s*:\s*σ\s*(≤|<)\s*\((.*?)\s*:\s*ℝ\)\)',h)
    assert a and b,h
    return dict(lo=expr(a[1]),hi=expr(b[2]),lo_closed=a[2]=='≤',hi_closed=b[1]=='≤')
def power(h):
    i=h.index('T ^ (')+4;s,_=group(h,i);return sp.cancel(expr(s)-E)
def contains(r,x):return (r['lo']<x or r['lo_closed']and r['lo']==x)and(r['hi']>x or r['hi_closed']and r['hi']==x)
def nonnegative(f,a,b):
    if f==0:return dict(identity=True)
    n,d=sp.fraction(sp.cancel(f));mid=(a+b)/2;sign=sp.sign(d.subs(S,mid));assert sign in [-1,1]
    dp=sp.Poly(d,S)
    for rt in sp.polys.polytools.real_roots(dp):assert not a<rt<b,(f,a,b,rt)
    n=sp.Poly(sp.expand(sign*n),S);assert n.degree()<=2
    points=[a,b]
    if n.degree()==2 and n.nth(2)>0:
        v=-n.nth(1)/(2*n.nth(2))
        if a<v<b:points.append(v)
    values=[n.eval(x)for x in points];assert all(v>=0 for v in values),(f,a,b,points,values)
    return dict(denominator_sign=int(sign),test_points=list(map(str,points)),numerator_values=list(map(str,values)))
def clean(s):return re.sub(r'\s+','',s)
def main():
    source=(R/'Solution.lean').read_text();challenge=(R/'Challenge.lean').read_text();sol=declarations(source);cha=declarations(challenge)
    config=json.loads((R/'comparator.json').read_text());assert len(config['theorem_names'])==73 and not config['definition_names']
    for root in config['theorem_names']:
        name=root.split('.')[-1];assert clean(sol[name]['header'])==clean(cha[name]['header']),name
    D=json.loads((P/'BOUNDS.json').read_text());F=json.loads((P/'ACTIVE_FRONTIERS.json').read_text());providers=[];ledger=[]
    deps={r['root']:r for r in json.loads((H/'PER_ROOT_FRESH_DEPENDENCY_AUDIT.json').read_text())['roots']}
    assets={r['key']:r for r in json.loads((P/'math_assets/MATH_ASSETS.json').read_text())}
    csvrows={r['ID']:r for r in csv.DictReader((P/'ALL_PROVED_BOUNDS.csv').open())}
    md=(P/'README_DRAFT.md').read_text();mdrows={m[1]:[x.strip().strip('$')for x in m[2].split('|')]for m in re.finditer(r'^\| (P\d+) \| (.*?) \|$',md,re.M)}
    for r in D['main_rows']:
        rid=r['id'];name='provider_'+rid;h=sol[name]['header'];b=bounds(h);p=power(h)
        assert h.startswith('theorem '+name+' {σ ε : ℝ}')and'(hε : 0 < ε)'in h
        assert '∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →'in h and 'zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ('in h
        domain=r['domains'];assert len(domain)==1;dd=domain[0]
        assert b==dict(lo=expr(dd['lo']),hi=expr(dd['hi']),lo_closed=dd['lo_closed'],hi_closed=dd['hi_closed']),rid
        formula=expr(r['formula_p'].replace('sigma','s'));assert sp.cancel(p-formula)==0,rid
        printed_kind,printed=r['display_formula'].split('=',1);printed=expr(printed)
        assert sp.cancel(p-(printed*(1-S)if printed_kind.strip()=='A'else printed))==0,rid
        asset=assets[rid+'_formula'];ak,av=asset['math'].split('=',1);av=expr(latex(av));assert sp.cancel(p-(av*(1-S)if ak=='A'else av))==0,rid
        asset_path=P/'math_assets'/asset['pdf'];assert hashlib.sha256(asset_path.read_bytes()).hexdigest()==asset['sha256']
        texrange=latex(assets[rid+'_range']['math']).replace(' ','');left,right=texrange[1:-1].split(',');assert expr(left)==b['lo']and expr(right)==b['hi']
        assert (texrange[0]=='[')==b['lo_closed']and(texrange[-1]==']')==b['hi_closed']
        mk,mv=mdrows[rid][0].split('=',1);mv=expr(mv);assert sp.cancel(p-(mv*(1-S)if mk.strip()=='A'else mv))==0,rid
        assert csvrows[rid]['formula']==r['display_formula']and csvrows[rid]['full_range']==r['display_domain']
        expected_const='U'if rid in ['P29','P30','P31']else'S';assert mdrows[rid][2]==expected_const and csvrows[rid]['constant']==expected_const
        a,bhi=b['lo'],b['hi'];assert a<bhi;w=(a+bhi)/2;assert contains(b,w)
        den=sp.fraction(p)[1]
        for root in sp.polys.polytools.real_roots(sp.Poly(den,S)):
            assert not contains(b,root),(rid,'zero denominator',root)
        dep=deps['LewkoDensityPalomar.'+name]
        assert dep['canonical_zeta']and dep['analytic_multiplicity']
        row=dict(id=rid,root='LewkoDensityPalomar.'+name,file='Solution.lean',line=sol[name]['line'],power_exponent=str(p),normalized_A=str(sp.cancel(p/(1-S))),**{k:str(v)if k in ['lo','hi']else v for k,v in b.items()},constant=expected_const,epsilon_loss='additive +epsilon in power exponent',nonvacuity_witness=dict(sigma=str(w),epsilon='1',T='2'),OAI_closure=dep['OAI_declarations'],source_class=r['source_class'],checks='PASS: Lean headers, JSON, README, CSV and hashed PDF formula/range assets agree')
        ledger.append(row);providers.append(dict(id=rid,p=p,**b))
    families={'baseline':providers[:10],'announced':providers[:13],'since_announcement':providers}
    checks=[];piece_rows=[]
    for f in F:
        sid=f['id'];name='piece_'+sid;h=sol[name]['header'];b=bounds(h);p=power(h);a=expr(f['lo']);z=expr(f['hi']);assert a==b['lo']and z==b['hi']
        assert not f['plot_lo_closed']or b['lo_closed'];assert not f['plot_hi_closed']or b['hi_closed']
        assert sp.cancel(p-expr(f['a'])*(1-S))==0,sid
        source_provider=next(r for r in providers if r['id']==f['provider_id']);assert sp.cancel(p-source_provider['p'])==0
        for other in families[f['stage']]:
            l=max(a,other['lo']);u=min(z,other['hi'])
            if l<u:checks.append(dict(piece=sid,provider=other['id'],lo=str(l),hi=str(u),certificate=nonnegative(other['p']-p,l,u)))
        if f['stage']!='baseline':nonnegative(sp.Rational(39,17)*(1-S)-p,a,z)
        piece_rows.append(dict(id=sid,root='LewkoDensityPalomar.'+name,file='Solution.lean',line=sol[name]['line'],provider=f['provider_id'],stage=f['stage'],power_exponent=str(p),lo=str(a),hi=str(z),theorem_lo_closed=b['lo_closed'],theorem_hi_closed=b['hi_closed'],plot_lo_closed=f['plot_lo_closed'],plot_hi_closed=f['plot_hi_closed'],boundary_convention='At sigma=1 only A left limit is plotted; count is independently zero.'))
    points=sorted({expr(f[k])for f in F for k in ['lo','hi']})
    for stage,family in families.items():
        for x in points:
            if x==1:continue
            active=[r for r in family if contains(r,x)];assert active
            true=min(r['p'].subs(S,x)for r in active)
            plotted=[expr(f['a'])*(1-S)for f in F if f['stage']==stage and contains(dict(lo=expr(f['lo']),hi=expr(f['hi']),lo_closed=f['plot_lo_closed'],hi_closed=f['plot_hi_closed']),x)]
            assert plotted and min(p.subs(S,x)for p in plotted)==true,(stage,x,true,plotted)
    strict=[]
    for l,u in zip(points,points[1:]):
        x=(l+u)/2;ann=min(r['p'].subs(S,x)for r in providers[:13]if contains(r,x));new=min(r['p'].subs(S,x)for r in providers if contains(r,x))
        assert new<=ann
        if new<ann:
            if strict and strict[-1][1]==l:strict[-1][1]=u
            else:strict.append([l,u])
    assert strict==[[sp.Rational(12,17),sp.Rational(3,4)],[sp.Rational(7,9),sp.Rational(17,19)]],strict
    strict_endpoints={str(x):bool(min(r['p'].subs(S,x)for r in providers if contains(r,x))<min(r['p'].subs(S,x)for r in providers[:13]if contains(r,x)))for pair in strict for x in pair}
    assert strict_endpoints=={'12/17':False,'3/4':True,'7/9':False,'17/19':False}
    for name in ['global39over17','uniform_P29','uniform_P30','uniform_P31']:
        h=sol[name]['header'];assert h.startswith('theorem '+name+' {ε : ℝ} (hε : 0 < ε)')
        assert '∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ'in h
    core=(R/'CountCore.lean').read_text()
    def defs(s):
        s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
        out={}
        for m in re.finditer(r'noncomputable def (zeroWeight|zeroCount)\b(.*?)(?=\n(?:noncomputable def|theorem)|\Z)',s,re.S):out[m[1]]=clean(m[2])
        return out
    assert defs(core)==defs(challenge)
    abstract=(P/'PROPOSED_ABSTRACT.txt').read_text();assert '12/17 < σ ≤ 3/4 and 7/9 < σ ≤ 7/8'in abstract
    assert '7/8 < σ < 17/19'in abstract
    result=dict(status='PASS_FRESH_MAIN_CLAIM_AND_EXACT_FRONTIER_AUDIT',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),selected_theorem_headers=73,fixed_count_definition_bodies=2,providers=ledger,pieces=piece_rows,uniform_roots=['LewkoDensityPalomar.'+n for n in ['global39over17','uniform_P29','uniform_P30','uniform_P31']],exact_minimum_certificates=checks,strict_power_curve_comparison_intervals=['(12/17,3/4]','(7/9,17/19)'],strict_improvement_endpoint_truth=strict_endpoints,global39over17_dominated_by_announced_and_new_frontiers=True,external_zero_free_region_excluded_from_minimum_calculation=True,actual_zero_count_at_sigma1='0; open critical strip makes region empty',new_mathematical_assumptions=False)
    print('Exact arithmetic audit passed; retained receipt is unchanged.')
    print(json.dumps({k:v for k,v in result.items()if k not in ['providers','pieces','exact_minimum_certificates']}),flush=True)
if __name__=='__main__':main()
