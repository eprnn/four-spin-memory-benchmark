"""Draw the star's two upper bounds and three analytically identified cases."""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

matplotlib.rcParams.update({"pdf.fonttype": 42, "font.family": "DejaVu Sans"})
swaps = []
for leaf in (1, 2, 3):
    order = list(range(4))
    order[0], order[leaf] = order[leaf], order[0]
    swaps.append(np.eye(4)[order])
attack = np.linalg.eigh(-swaps[0]+(swaps[1]+swaps[2])/2)[1][:, -1]
attack_yes = (3 - attack @ sum(swaps) @ attack)/6
alpha = .5+(1+np.sqrt(33))/24
assert np.isclose(attack_yes, .373147, atol=1e-6)

fig, ax = plt.subplots(figsize=(5.7, 2.75))
fig.subplots_adjust(left=.13, right=.97, bottom=.23, top=.96)
q = np.linspace(.32, .60, 600)
bound = np.minimum(alpha, 1-q/2)
ax.fill_between(q, bound, 1.025, color="#edf4f5")
ax.plot(q, np.full_like(q, alpha), color="#7c7d80", ls=":", lw=1.4)
ax.plot(q, 1-q/2, color="#537783", ls="--", lw=1.2)
ax.plot(q, bound, color="#195565", lw=2)
ax.scatter([attack_yes, .5], [alpha, .75], s=25, facecolor="white",
           edgecolor="#195565", lw=1.35, zorder=4)
ax.scatter([.5], [1], marker="D", color="#A64D28", s=22, zorder=4)
ax.annotate("Optimal star replacement", (attack_yes, alpha), xytext=(-22,-17),
            textcoords="offset points", fontsize=8.5)
ax.annotate("Code-space replacement", (.5,.75), xytext=(3,-18),
            textcoords="offset points", fontsize=8.5, ha="center")
ax.annotate("Ideal transmission", (.5,1), xytext=(-8,-2),
            textcoords="offset points", ha="right", va="center", fontsize=8)
ax.text(.458,.903,"Excluded for measure-and-prepare", ha="center", fontsize=8.5, color="#195565")
ax.set(xlim=(.32,.60),ylim=(.69,1.025),xlabel="Mean singlet probability across the three settings",
       ylabel="Match probability")
ax.set_xticks([.35,.40,.45,.50,.55,.60])
ax.set_yticks([.70,.75,.80,.85,.90,.95,1.0])
ax.tick_params(labelsize=8.5, length=3)
ax.xaxis.label.set_size(8.5)
ax.yaxis.label.set_size(8.5)
for name in ("top","right"):
    ax.spines[name].set_visible(False)
fig.savefig(Path(__file__).with_name("star-data.pdf"), metadata={"CreationDate":None,"ModDate":None})
