# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Generate all 4 publication-grade vector PDF figures and the 1280x640 social preview PNG
directly from verified exact computations (zero fabricated data)."""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))

from pfa_verify.exact_core import (
    bloch_matrix4,
    gardam_alpha,
    ronkin_function,
    run_all_verifications,
    spectral_winding,
    track_braid_loop,
)

# Colorblind-safe Okabe-Ito palette
C_BLUE = "#0072B2"
C_ORANGE = "#E69F00"
C_VERM = "#D55E00"
C_GREEN = "#009E73"
C_PURPLE = "#CC79A7"
C_SKY = "#56B4E9"
C_DARK = "#1B2432"

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.5,
    "axes.labelsize": 9.5,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "legend.fontsize": 8.0,
    "figure.dpi": 300,
    "savefig.bbox": "tight",
    "pdf.fonttype": 42,
})


def make_fig1(report: dict, fig_dir: Path) -> None:
    """Fig 1: Haah Cubic Code Prime-Characteristic Bifurcation & Signed Class m=1 Singularity."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 3.9))

    # Panel A: CC1 (m=0) k_logical(L, p) across primes p = 2, 3, 5, 7, 11, 13
    Ls = list(range(2, 16))
    styles = [
        ("2", C_DARK, "-o", r"$p=2$ ($\mathbb{F}_4$ split)"),
        ("3", C_VERM, "-s", r"$p=3$ ($2p=6 \Rightarrow 18$)"),
        ("5", C_BLUE, "-^", r"$p=5$ ($2p=10 \Rightarrow 30$)"),
        ("7", C_GREEN, "-D", r"$p=7$ ($2p=14 \Rightarrow 42$)"),
        ("11", C_PURPLE, "--v", r"$p=11$ ($L=10 \Rightarrow 12$)"),
        ("13", C_ORANGE, ":x", r"$p=13$ ($L=12 \Rightarrow 24$)"),
    ]
    for p_str, col, fmt, lbl in styles:
        ys = [report["haah_cc1_k_logical"][p_str][str(L)] for L in Ls]
        ax1.plot(Ls, ys, fmt, color=col, linewidth=1.6, markersize=4.5, label=lbl, alpha=0.92)
    ax1.annotate(r"Frobenius $6p$ jumps", xy=(14, 42), xytext=(8.8, 43.5),
                 arrowprops={"arrowstyle": "->", "color": C_GREEN, "lw": 1.1},
                 fontsize=8.2, color=C_GREEN, fontweight="bold")
    ax1.annotate(r"First odd-$L$ rational root:" + "\n" + r"$p=23, L=11 \Rightarrow k=6$",
                 xy=(11, 0.3), xytext=(7.6, 33.5),
                 bbox={"boxstyle": "round,pad=0.3", "fc": "#FFF8E7", "ec": C_ORANGE, "lw": 0.9},
                 arrowprops={"arrowstyle": "->", "color": C_ORANGE, "lw": 1.0},
                 fontsize=7.8, color=C_DARK)
    ax1.set_title(r"(a) Haah $\mathrm{CC1}$ ($m=0$, $\det(2Q)=+8$): $\log_p \mathrm{GSD}_p(L)$")
    ax1.set_xlabel(r"Linear torus size $L$")
    ax1.set_ylabel(r"Logical qudits $k_p(L) = \log_p \mathrm{GSD}_p(L)$")
    ax1.set_xticks(Ls)
    ax1.set_ylim(-2, 54)
    ax1.grid(True, linestyle=":", alpha=0.45)
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92, ncol=1)

    # Panel B: Signed Class m=1 (1,1,1, 1,1,-1) with det(2Q) = -12 (singular at p=3!)
    Ls2 = list(range(2, 13))
    styles2 = [
        ("2", C_DARK, "-o", r"$p=2$ ($\mathbb{F}_4$ split)"),
        ("3", C_VERM, "-s", r"$p=3$ (SINGULAR $\mathbb{F}_9$ split!)"),
        ("5", C_BLUE, "-^", r"$p=5$ (smooth conic)"),
        ("7", C_GREEN, "-D", r"$p=7$ (smooth conic)"),
        ("11", C_PURPLE, "--v", r"$p=11$ ($L=5 \Rightarrow k=4$)"),
    ]
    for p_str, col, fmt, lbl in styles2:
        ys = [report["haah_m1_singular_p3_k_logical"][p_str][str(L)] for L in Ls2]
        lw = 2.2 if p_str == "3" else 1.4
        ax2.plot(Ls2, ys, fmt, color=col, linewidth=lw, markersize=4.8, label=lbl, alpha=0.92)
    ax2.annotate(r"$p=3$ $\mathbb{F}_9$ split:" + "\n" + r"$L=8 \Rightarrow k_3(8)=24$",
                 xy=(8, 24), xytext=(8.6, 25.0),
                 bbox={"boxstyle": "round,pad=0.25", "fc": "#FFF5F0", "ec": C_VERM, "lw": 0.9},
                 arrowprops={"arrowstyle": "->", "color": C_VERM, "lw": 1.2},
                 fontsize=8.0, color=C_VERM, fontweight="bold")
    ax2.set_title(r"(b) Signed Class $m=1$ ($\det(2Q)=-12$): $p=3$ Degeneration")
    ax2.set_xlabel(r"Linear torus size $L$")
    ax2.set_ylabel(r"Logical qudits $k_p(L)$")
    ax2.set_xticks(Ls2)
    ax2.set_ylim(-1.5, 33)
    ax2.grid(True, linestyle=":", alpha=0.45)
    ax2.legend(loc="upper left", frameon=True, framealpha=0.92)

    fig.tight_layout()
    fig.savefig(fig_dir / "fig1_haah_prime_bifurcation.pdf")
    plt.close(fig)


def make_fig2(report: dict, fig_dir: Path) -> None:
    """Fig 2: Gardam 8-Sign-Point Landscape, P1^2 - 31 Obstruction, & 2-Adic Hensel Tower."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 3.8))

    # Panel A: Parabolic obstruction N1(P1) = P1^2 - 31 vs +-1 band
    xs = np.arange(-8, 9)
    ys = xs**2 - 31
    ax1.axhline(1, color=C_VERM, linestyle="--", linewidth=1.1, label=r"Unit target $N_1 = \pm 1$")
    ax1.axhline(-1, color=C_VERM, linestyle="--", linewidth=1.1)
    ax1.axhspan(-1, 1, color=C_VERM, alpha=0.14)
    ax1.plot(xs, ys, "-o", color=C_BLUE, linewidth=1.8, markersize=5.0,
             label=r"$N_1(P_1) = P_1^2 - 31$ ($P_1 \in \mathbb{Z}$)")
    # Highlight closest misses P1 = +-5 (-6) and P1 = +-6 (+5)
    for px, py, off in [(5, -6, (0.4, -10)), (6, 5, (-3.1, 9))]:
        ax1.scatter([px, -px], [py, py], color=C_ORANGE, s=60, zorder=5)
        ax1.annotate(rf"$P_1=\pm {px} \Rightarrow N_1={py:+d}$",
                     xy=(px, py), xytext=(px + off[0], py + off[1]),
                     arrowprops={"arrowstyle": "->", "color": C_DARK, "lw": 0.9},
                     fontsize=8.0, fontweight="bold")
    ax1.set_title(r"(a) Strengthened $2^{21}$ No-Sign-Lift Obstruction ($5^2 < 30, 32 < 6^2$)")
    ax1.set_xlabel(r"Arbitrary even coset evaluation $P_1 = P(1, 1, -1) \in \mathbb{Z}$")
    ax1.set_ylabel(r"Quaternionic norm $N_1 = P_1^2 - Q_1^2 - R_1^2 + S_1^2$")
    ax1.set_ylim(-36, 40)
    ax1.grid(True, linestyle=":", alpha=0.45)
    ax1.legend(loc="upper center", frameon=True)

    # Panel B: 2-Adic Hensel Inverse Support Growth mod 2^m (m = 1..6)
    ms = [1, 2, 3, 4, 5, 6]
    sups = [report["hensel_2adic_supports"][f"mod_{1 << m}"] for m in ms]
    ax2.bar(ms, sups, color=[C_DARK, C_BLUE, C_SKY, C_GREEN, C_ORANGE, C_VERM],
            edgecolor=C_DARK, linewidth=0.8, width=0.62)
    for m, s in zip(ms, sups):
        ax2.text(m, s * 1.07, f"{s:,}", ha="center", va="bottom", fontsize=8.0, fontweight="bold")
    ax2.set_yscale("log")
    ax2.set_ylim(10, 12000)
    ax2.set_xticks(ms)
    ax2.set_xticklabels([rf"$2^{m}$" + f"\n(mod {1 << m})" for m in ms])
    ax2.set_title(r"(b) Exact 2-Adic Hensel Tower Support $|\mathrm{supp}(\beta_m)|$ in $(\mathbb{Z}/2^m\mathbb{Z})[P]$")
    ax2.set_xlabel(r"Modulus $2^m$ (exact inverse $\tilde{\alpha}\beta_m \equiv 1\;(\mathrm{mod}\;2^m)$)")
    ax2.set_ylabel(r"Inverse support size $|\mathrm{supp}(\beta_m)|$ (log scale)")
    ax2.grid(True, which="both", axis="y", linestyle=":", alpha=0.45)

    fig.tight_layout()
    fig.savefig(fig_dir / "fig2_gardam_sign_lift_obstruction.pdf")
    plt.close(fig)


def make_fig3(fig_dir: Path) -> dict:
    """Fig 3: V4-Symmetric Ronkin Surface, Bipolar Skin Winding Map, and Haah Double-Amoeba."""
    m = bloch_matrix4(gardam_alpha())
    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(11.6, 3.55))

    # Panel A: Ronkin slices R(mu_x, 0, 0), R(0, mu_y, 0), R(0, 0, mu_z)
    mus = np.linspace(-0.9, 0.9, 19)
    rx = [ronkin_function(m, (float(u), 0.0, 0.0), 10) for u in mus]
    rz = [ronkin_function(m, (0.0, 0.0, float(u)), 10) for u in mus]
    ax1.plot(mus, rx, "-o", color=C_BLUE, markersize=3.5, lw=1.7, label=r"$R(\mu, 0, 0) = R(0, \mu, 0)$")
    ax1.plot(mus, rz, "-s", color=C_VERM, markersize=3.5, lw=1.7, label=r"$R(0, 0, \mu)$")
    ax1.axhline(0.0, color=C_GREEN, linestyle="--", lw=1.2, label=r"Mod-2 collapse $R_{\mathbb{F}_2} \equiv 0$")
    r0_16 = ronkin_function(m, (0.0, 0.0, 0.0), 16)
    ax1.scatter([0.0], [rx[9]], color=C_ORANGE, s=55, zorder=6)
    ax1.annotate(r"Global min $\mu=0$" + "\n" + rf"$R(0) \approx {r0_16:.3f}$",
                 xy=(0.0, rx[9]), xytext=(-0.55, 2.3),
                 arrowprops={"arrowstyle": "->", "color": C_DARK, "lw": 1.0},
                 fontsize=7.8, fontweight="bold")
    ax1.set_title(r"(a) $V_4$-Convex Ronkin Function $R(\mu)$")
    ax1.set_xlabel(r"Imaginary flux $\mu$")
    ax1.set_ylabel(r"Ronkin potential $R(\mu)$")
    ax1.set_ylim(-0.4, 5.6)
    ax1.grid(True, linestyle=":", alpha=0.45)
    ax1.legend(loc="lower right", fontsize=7.2)

    # Panel B: 2D Bipolar Skin Winding Map W_x(k_y, k_z) at E=0 (odd under k_z -> -k_z!)
    ng = 25
    ks = np.linspace(-math.pi, math.pi, ng, endpoint=False) + math.pi / ng
    wmap = np.zeros((ng, ng), dtype=float)
    for iy, ky in enumerate(ks):
        for iz, kz in enumerate(ks):
            w, mg = spectral_winding(m, "x", float(ky), float(kz), 0j, npts=384)
            wmap[iz, iy] = round(w) if (mg > 0.35 and abs(w - round(w)) < 0.05) else 0.0
    im = ax2.imshow(
        wmap,
        origin="lower",
        extent=[-math.pi, math.pi, -math.pi, math.pi],
        cmap="RdBu_r",
        vmin=-2,
        vmax=2,
        aspect="equal",
        interpolation="nearest",
    )
    ax2.axhline(0, color="k", lw=0.7, ls="--", alpha=0.6)
    ax2.axvline(0, color="k", lw=0.7, ls="--", alpha=0.6)
    cbar = fig.colorbar(im, ax=ax2, fraction=0.046, pad=0.04, ticks=[-2, -1, 0, 1, 2])
    cbar.set_label(r"$W_x(k_y, k_z)$")
    ax2.set_title(r"(b) Bipolar Skin Map $W_x(k_y,-k_z) = -W_x$")
    ax2.set_xlabel(r"$k_y$")
    ax2.set_ylabel(r"$k_z$")
    ax2.set_xticks([-math.pi, 0, math.pi])
    ax2.set_xticklabels([r"$-\pi$", r"$0$", r"$\pi$"])
    ax2.set_yticks([-math.pi, 0, math.pi])
    ax2.set_yticklabels([r"$-\pi$", r"$0$", r"$\pi$"])

    # Panel C: Exact Haah Double-Amoeba Cross-Section A(f) and A(g) at mu_z = 0 (r_z = 1)
    u = np.linspace(-2.4, 2.4, 300)
    UX, UY = np.meshgrid(u, u)
    RX, RY, RZ = np.exp(UX), np.exp(UY), 1.0
    in_f = (1 <= RX + RY + RZ) & (RX <= 1 + RY + RZ) & (RY <= 1 + RX + RZ) & (RZ <= 1 + RX + RY)
    in_g = (
        (1 <= RX * RY + RY * RZ + RZ * RX)
        & (RX * RY <= 1 + RY * RZ + RZ * RX)
        & (RY * RZ <= 1 + RX * RY + RZ * RX)
        & (RZ * RX <= 1 + RX * RY + RY * RZ)
    )
    state = np.zeros_like(UX, dtype=int)
    state[in_f] = 1
    state[in_g] = 2
    state[in_f & in_g] = 3
    from matplotlib.colors import ListedColormap
    cmap3 = ListedColormap(["#F7F9FC", C_SKY, C_ORANGE, C_PURPLE])
    ax3.imshow(state, origin="lower", extent=[-2.4, 2.4, -2.4, 2.4], cmap=cmap3, vmin=0, vmax=3, aspect="equal")
    ax3.scatter([0.0], [0.0], color=C_DARK, s=30, zorder=5)
    ax3.text(0.12, 0.12, r"$\mathcal{A}(f)\cap\mathcal{A}(g)$", fontsize=7.6, color="white", fontweight="bold")
    ax3.text(-2.2, 1.9, r"$\mathcal{A}(g)$", fontsize=8.0, color=C_DARK, fontweight="bold")
    ax3.text(1.3, -2.1, r"$\mathcal{A}(f)$", fontsize=8.0, color=C_DARK, fontweight="bold")
    ax3.set_title(r"(c) Haah Double-Amoeba ($\mu_z = 0$)")
    ax3.set_xlabel(r"$\mu_x = \ln r_x$")
    ax3.set_ylabel(r"$\mu_y = \ln r_y$")

    fig.tight_layout()
    fig.savefig(fig_dir / "fig3_nonhermitian_amoeba_ronkin.pdf")
    plt.close(fig)
    return {
        "wmap_nonzero_fraction": float(np.mean(wmap != 0)),
        "wmap_antisymmetry_max_err": float(np.max(np.abs(wmap + wmap[::-1, :]))),
    }


def make_fig4(fig_dir: Path) -> None:
    """Fig 4: 4-Band Complex Eigenvalue Braids Generating Full S_4 on Gardam's Crystal."""
    m = bloch_matrix4(gardam_alpha())
    configs = [
        ("x", 0.3, 0.7, r"(a) Loop $k_x$ $(0.3, 0.7)$: $(1\;2)$, $\deg_\Delta = -1$"),
        ("x", 1.0, 1.5, r"(b) Loop $k_x$ $(1.0, 1.5)$: $(0\;2\;1\;3)$, $\deg_\Delta = -3$"),
        ("z", 2.0, 1.0, r"(c) Loop $k_z$ $(2.0, 1.0)$: $(0\;1)(2\;3)$, $\deg_\Delta = -2$"),
    ]
    band_colors = [C_BLUE, C_VERM, C_GREEN, C_ORANGE]
    fig = plt.figure(figsize=(12.2, 4.0))
    for idx, (axis, f1, f2, title) in enumerate(configs, start=1):
        ax = fig.add_subplot(1, 3, idx, projection="3d")
        res = track_braid_loop(m, axis, f1, f2, nsteps=360)
        ts = np.linspace(0, 2 * math.pi, len(res["trajectories"][0]))
        for b_idx, traj in enumerate(res["trajectories"]):
            re = [z.real for z in traj]
            im = [z.imag for z in traj]
            ax.plot(re, im, ts, color=band_colors[b_idx], linewidth=1.8, label=rf"$\lambda_{b_idx}$")
        ax.set_title(title, fontsize=9.2, pad=8)
        ax.set_xlabel(r"$\mathrm{Re}\,\lambda$", fontsize=8.0, labelpad=3)
        ax.set_ylabel(r"$\mathrm{Im}\,\lambda$", fontsize=8.0, labelpad=3)
        ax.set_zlabel(rf"$k_{axis}$", fontsize=8.0, labelpad=3)
        if idx == 1:
            ax.set_xticks([0, 5, 10, 15])
        ax.set_zticks([0, math.pi, 2 * math.pi])
        ax.set_zticklabels([r"$0$", r"$\pi$", r"$2\pi$"])
        ax.view_init(elev=22, azim=-52)
        ax.tick_params(labelsize=7.2)
        if idx == 1:
            ax.legend(loc="upper left", fontsize=7.0, ncol=2)
    fig.subplots_adjust(left=0.02, right=0.98, wspace=0.22, top=0.88, bottom=0.06)
    fig.savefig(fig_dir / "fig4_b4_eigenvalue_braids.pdf")
    plt.close(fig)


def make_social_preview(fig_dir: Path, media_dir: Path) -> None:
    """1280x640 high-contrast social preview card (Build Standard A26)."""
    m = bloch_matrix4(gardam_alpha())
    fig = plt.figure(figsize=(12.8, 6.4), dpi=100, facecolor="#0B1020")
    gs = fig.add_gridspec(1, 2, width_ratios=[1.38, 0.92], wspace=0.06, left=0.03, right=0.98, top=0.94, bottom=0.06)

    ax_txt = fig.add_subplot(gs[0])
    ax_txt.set_facecolor("#0B1020")
    ax_txt.axis("off")
    ax_txt.set_xlim(0, 1)
    ax_txt.set_ylim(0, 1)
    ax_txt.text(0.02, 0.89, "PROMISLOW-FRACTON-AMOEBA", color="#56B4E9",
                fontsize=21, fontweight="bold", family="sans-serif")
    ax_txt.text(0.02, 0.77, "Hantzsche-Wendt Group Rings, All-Prime Type-II Fractons,\n"
                            "and 3D Non-Hermitian B4 Eigenvalue Monodromy",
                color="#E6EDF3", fontsize=12.5, family="sans-serif")
    bullets = [
        "15 Zero-Mathlib Lean 4.35.0 Theorems + 6 Independent Kernels",
        "Strengthened 2^21 No-Sign-Lift Obstruction (P1^2 not in {30, 32})",
        "All-Prime (p >= 2) Type-II No-Strings Proof for Haah CC1 (Bezout = 2)",
        "First Non-Abelian Gardam-Twisted & Intrinsic HW Fracton Codes",
        "V4-Convex Ronkin Origin-Minimum Law & Full S4 Braid Monodromy",
        "Zero-Dependency Rust Core + Real-Time 3D WebGL2 Studio",
    ]
    for i, b in enumerate(bullets):
        ax_txt.text(0.03, 0.61 - i * 0.088, f">  {b}", color="#C9D1D9",
                    fontsize=10.3, family="sans-serif")
    ax_txt.text(0.02, 0.04, "Alexander Stephen Donahue  |  ORCID 0009-0006-8168-9648  |  v1.0.0",
                color="#8B949E", fontsize=9.8, family="monospace")

    ax3d = fig.add_subplot(gs[1], projection="3d", facecolor="#0B1020")
    res = track_braid_loop(m, "x", 1.0, 1.5, nsteps=360)
    ts = np.linspace(0, 2 * math.pi, len(res["trajectories"][0]))
    for col, traj in zip(["#56B4E9", "#FF7B72", "#3FB950", "#F0B429"], res["trajectories"]):
        ax3d.plot([z.real for z in traj], [z.imag for z in traj], ts, color=col, lw=2.6)
    ax3d.set_title("4-Band B4 Eigenvalue Braid (0 2 1 3), deg = -3", color="#E6EDF3", fontsize=12)
    ax3d.xaxis.pane.fill = False
    ax3d.yaxis.pane.fill = False
    ax3d.zaxis.pane.fill = False
    ax3d.tick_params(colors="#8B949E", labelsize=8)
    ax3d.set_xlabel("Re(λ)", color="#C9D1D9")
    ax3d.set_ylabel("Im(λ)", color="#C9D1D9")
    ax3d.set_zlabel("kx", color="#C9D1D9")
    ax3d.view_init(elev=22, azim=-48)

    media_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(media_dir / "social-preview.png", facecolor="#0B1020")
    plt.close(fig)


def main() -> None:
    fig_dir = ROOT / "paper" / "figures"
    media_dir = ROOT / "docs" / "media"
    fig_dir.mkdir(parents=True, exist_ok=True)
    report = run_all_verifications(ROOT / "results")
    make_fig1(report, fig_dir)
    make_fig2(report, fig_dir)
    fig3_stats = make_fig3(fig_dir)
    make_fig4(fig_dir)
    make_social_preview(fig_dir, media_dir)
    (ROOT / "results" / "fig3_bipolar_stats.json").write_text(
        json.dumps(fig3_stats, indent=2) + "\n", encoding="utf-8"
    )
    print("Generated all 4 vector PDF figures + social-preview.png:", fig3_stats)


if __name__ == "__main__":
    main()
