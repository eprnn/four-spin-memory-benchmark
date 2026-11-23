"""Regenerate the vector figure showing two receivers on the same four sites."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

matplotlib.rcParams.update({"pdf.fonttype": 42, "font.family": "DejaVu Sans"})
positions = {1: (0, 1), 2: (1.28, 1), 3: (1.28, 0), 4: (0, 0)}
fig, axes = plt.subplots(1, 2, figsize=(5.7, 2.02))
fig.subplots_adjust(left=.025, right=.975, top=.81, bottom=.15, wspace=.38)
for ax, name, third, ceiling in zip(axes, ("Star receiver", "Triangle receiver"),
                                    ((1, 4), (2, 3)), ("78.1023%", "75%")):
    ax.set_aspect("equal")
    ax.set_xlim(-.31, 1.59)
    ax.set_ylim(-.22, 1.22)
    ax.set_axis_off()
    for (i, j), color, style in zip(((1, 2), (1, 3), third),
                                     ("#215876", "#37765E", "#A64D28"),
                                     ("-", "--", "-.")):
        x, y = zip(positions[i], positions[j])
        ax.plot(x, y, color=color, linestyle=style, linewidth=2.3, solid_capstyle="round")
    for site, (x, y) in positions.items():
        unused = site == 4 and third == (2, 3)
        ax.add_patch(Circle((x, y), .142, facecolor="white",
                            edgecolor="#80888C" if unused else "#26353B", lw=1.15, zorder=3))
        ax.text(x, y, str(site), ha="center", va="center", fontsize=9.5,
                color="#656A6E" if unused else "#192328", zorder=4)
    ax.set_title(name, fontsize=10, weight="bold", pad=7, color="#192328")
    ax.text(.5, -.1, f"Classical ceiling  {ceiling}", transform=ax.transAxes,
            fontsize=8.5, ha="center", va="top", color="#26353B")
fig.savefig(Path(__file__).with_name("wiring.pdf"), metadata={"CreationDate": None, "ModDate": None})
