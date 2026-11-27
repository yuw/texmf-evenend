import sys,re,subprocess
# 同じ段（x位置）で，行の箱が縦に重なる所を数える
out=subprocess.run(['pdftotext','-bbox-layout',sys.argv[1],'-'],capture_output=True,text=True).stdout
bad=0; pg=0
for page in out.split('<page ')[1:]:
    pg+=1
    lines=[tuple(map(float,m)) for m in re.findall(r'<line xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)"',page)]
    for i,a in enumerate(lines):
        for b in lines[i+1:]:
            if min(a[2],b[2])-max(a[0],b[0])>20:
                ov=min(a[3],b[3])-max(a[1],b[1])
                if ov>3: bad+=1; print(' p%d overlap %.1f at y=%.0f'%(pg,ov,max(a[1],b[1])))
print('overlaps',bad)
