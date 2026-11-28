"""A scientific visualization of the exact rational signed continuation."""
from fractions import Fraction as F
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from polygon_extension import six_width,hole_triangle,upper_preimages,upper_patch

p,q,w=F(69,56),F(25,28),F(3,28)
T=six_width(p,q,w);H=hole_triangle(p,q,w)
K=upper_patch(H,p,q,w,F(1,1000));W=upper_preimages(K)
b=1/(2*p);S0=F(1,2)+b
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'svg.fonttype':'none'})
fig,axs=plt.subplots(1,3,figsize=(15,5),layout='constrained')
old='#465D87';new='#D47A2C';hole='#17857E'
def poly(ax,points,color,alpha=1,label=None):
    ax.add_patch(Polygon([(float(x),float(y))for x,y in points],closed=True,
                         facecolor=color,edgecolor=color,linewidth=1,alpha=alpha,label=label))
for i,P in enumerate(T):poly(axs[0],P,old,.85,'Original block' if i==0 else None)
for i,P in enumerate(W):poly(axs[0],P,new,1,'Added upper triangles' if i==0 else None)
axs[0].set(xlim=(0,1),ylim=(-.5,.5),xlabel='Height s',ylabel='Angular lift a',
           title='The rational block and its extension')
axs[0].set_aspect('equal');axs[0].legend(loc='lower left',frameon=False)
poly(axs[1],H,hole,.18,'H outside T + T')
poly(axs[1],K,hole,.6,'Truncated triangle K')
axs[1].set(xlim=(.806,.846),ylim=(.466,.503),xlabel='Sum height',ylabel='Sum angular lift',
           title='Exact positive-area sumset hole')
axs[1].set_aspect('equal');axs[1].legend(loc='lower left',frameon=False)
for P in T:poly(axs[2],P,old,.85)
for P in W:poly(axs[2],P,new,1)
axs[2].axvline(float(S0),color='#666666',lw=.8,ls='--')
axs[2].text(float(S0)-.001,.263,'Original height cutoff',rotation=90,ha='right',va='top',color='#555555')
axs[2].set(xlim=(.879,.925),ylim=(.228,.266),xlabel='Height s',ylabel='Angular lift a',
           title='One of the two added triangles')
axs[2].set_aspect('equal')
for ax in axs:
    ax.spines[['top','right']].set_visible(False)
    ax.grid(alpha=.12)
fig.suptitle('Allowing signed arc offsets gives limiting area 579/1904 ≈ 0.3040966387',fontsize=14)
fig.text(.5,-.03,'The plotted patch uses η = 1/1000. Thin gaps needed for the old potential are omitted from the ideal polygon view.',ha='center',fontsize=9)
out=Path(__file__).parent
fig.savefig(out/'torus-extension.svg',bbox_inches='tight')
fig.savefig(out/'torus-extension.png',dpi=180,bbox_inches='tight')
print('Saved torus-extension.svg and torus-extension.png')
