// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander S. Donahue
//! Zero-dependency exact algebraic, 3D fracton, and non-Hermitian amoeba/braid engine.

use std::collections::BTreeMap;
use std::f64::consts::PI;

pub const SIGS: [(i32, i32, i32); 4] = [
    (1, 1, 1),
    (1, -1, -1),
    (-1, 1, -1),
    (-1, -1, 1),
];

pub const COSET_PROD: [[(i32, i32, i32, usize); 4]; 4] = [
    [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 0, 2), (0, 0, 0, 3)],
    [(0, 0, 0, 1), (1, 0, 0, 0), (0, 0, 0, 3), (1, 0, 0, 2)],
    [(0, 0, 0, 2), (-1, 1, -1, 3), (0, 1, 0, 0), (-1, 0, -1, 1)],
    [(0, 0, 0, 3), (0, -1, 1, 2), (0, -1, 0, 1), (0, 0, 1, 0)],
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ElemP {
    pub c: usize,
    pub ix: i32,
    pub iy: i32,
    pub iz: i32,
}

impl ElemP {
    pub const ONE: ElemP = ElemP { c: 0, ix: 0, iy: 0, iz: 0 };

    pub fn new(ix: i32, iy: i32, iz: i32, c: usize) -> Self {
        Self { c, ix, iy, iz }
    }

    pub fn mul(self, rhs: ElemP) -> ElemP {
        let (s1, s2, s3) = SIGS[self.c];
        let (dx, dy, dz, c3) = COSET_PROD[self.c][rhs.c];
        ElemP {
            c: c3,
            ix: self.ix + s1 * rhs.ix + dx,
            iy: self.iy + s2 * rhs.iy + dy,
            iz: self.iz + s3 * rhs.iz + dz,
        }
    }

    pub fn inv(self) -> ElemP {
        let (dx, dy, dz, _) = COSET_PROD[self.c][self.c];
        let (s1, s2, s3) = SIGS[self.c];
        ElemP {
            c: self.c,
            ix: -dx - s1 * self.ix,
            iy: -dy - s2 * self.iy,
            iz: -dz - s3 * self.iz,
        }
    }
}

pub type ZPElem = BTreeMap<ElemP, i64>;
pub type LPoly3 = BTreeMap<(i32, i32, i32), i64>;

pub fn zp_one() -> ZPElem {
    let mut m = BTreeMap::new();
    m.insert(ElemP::ONE, 1);
    m
}

pub fn zp_add(a: &ZPElem, b: &ZPElem, modulus: Option<i64>) -> ZPElem {
    let mut out = a.clone();
    for (&k, &v) in b {
        *out.entry(k).or_insert(0) += v;
    }
    zp_clean(out, modulus)
}

pub fn zp_sub(a: &ZPElem, b: &ZPElem, modulus: Option<i64>) -> ZPElem {
    let mut out = a.clone();
    for (&k, &v) in b {
        *out.entry(k).or_insert(0) -= v;
    }
    zp_clean(out, modulus)
}

pub fn zp_mul(a: &ZPElem, b: &ZPElem, modulus: Option<i64>) -> ZPElem {
    let mut out: ZPElem = BTreeMap::new();
    for (&g1, &v1) in a {
        for (&g2, &v2) in b {
            let prod = if let Some(m) = modulus {
                ((v1 as i128 * v2 as i128).rem_euclid(m as i128)) as i64
            } else {
                v1 * v2
            };
            *out.entry(g1.mul(g2)).or_insert(0) += prod;
        }
    }
    zp_clean(out, modulus)
}

pub fn zp_star(a: &ZPElem) -> ZPElem {
    let mut out = BTreeMap::new();
    for (&g, &v) in a {
        out.insert(g.inv(), v);
    }
    out
}

fn zp_clean(mut m: ZPElem, modulus: Option<i64>) -> ZPElem {
    m.retain(|_, v| {
        if let Some(md) = modulus {
            *v = v.rem_euclid(md);
        }
        *v != 0
    });
    m
}

pub fn gardam_alpha() -> ZPElem {
    let raw = [
        (0,0,0,0),(1,0,0,0),(0,1,0,0),(1,1,0,0),(0,0,-1,0),(1,0,-1,0),(0,1,-1,0),(1,1,-1,0),
        (-1,-1,0,1),(1,0,0,1),(0,-1,1,1),(0,0,1,1),
        (0,0,0,2),(1,0,0,2),(0,-1,1,2),(1,1,1,2),
        (0,0,0,3),(1,0,-1,3),(-1,0,-1,3),(0,1,-1,3),(0,-1,-1,3),
    ];
    let mut m = BTreeMap::new();
    for (i, j, k, c) in raw {
        m.insert(ElemP::new(i, j, k, c), 1);
    }
    m
}

pub fn gardam_beta() -> ZPElem {
    let raw = [
        (-1,-1,0,0),(-1,-1,1,0),(-1,0,0,0),(-1,0,1,0),(0,-1,0,0),(0,-1,1,0),(0,0,0,0),(0,0,1,0),
        (-2,-1,0,1),(-1,-1,1,1),(-1,0,1,1),(0,0,0,1),
        (0,-2,1,2),(0,-1,0,2),(1,-1,0,2),(1,0,1,2),
        (-1,0,0,3),(0,-1,0,3),(0,0,-1,3),(0,1,0,3),(1,0,0,3),
    ];
    let mut m = BTreeMap::new();
    for (i, j, k, c) in raw {
        m.insert(ElemP::new(i, j, k, c), 1);
    }
    m
}

/// Hensel-lift Gardam's inverse modulo `2^m` (exact in `(Z / 2^m Z)[P]`).
pub fn gardam_hensel_inverse(m_bits: u32) -> (ZPElem, bool) {
    let modulus = 1i64 << m_bits;
    let a = gardam_alpha();
    let b0 = gardam_beta();
    // Newton-Hensel doubling: b_{k+1} = b_k * (2 - a * b_k) mod 2^m
    let mut b = b0;
    let mut two = BTreeMap::new();
    two.insert(ElemP::ONE, 2);
    for _ in 0..m_bits {
        let ab = zp_mul(&a, &b, Some(modulus));
        let factor = zp_sub(&two, &ab, Some(modulus));
        b = zp_mul(&b, &factor, Some(modulus));
    }
    let check_r = zp_mul(&a, &b, Some(modulus)) == zp_one();
    let check_l = zp_mul(&b, &a, Some(modulus)) == zp_one();
    (b, check_r && check_l)
}

pub fn lp_add(a: &LPoly3, b: &LPoly3) -> LPoly3 {
    let mut out = a.clone();
    for (&k, &v) in b {
        *out.entry(k).or_insert(0) += v;
    }
    out.retain(|_, v| *v != 0);
    out
}

pub fn lp_sub(a: &LPoly3, b: &LPoly3) -> LPoly3 {
    let mut out = a.clone();
    for (&k, &v) in b {
        *out.entry(k).or_insert(0) -= v;
    }
    out.retain(|_, v| *v != 0);
    out
}

pub fn lp_mul(a: &LPoly3, b: &LPoly3) -> LPoly3 {
    let mut out: LPoly3 = BTreeMap::new();
    for (&(x1, y1, z1), &v1) in a {
        for (&(x2, y2, z2), &v2) in b {
            *out.entry((x1 + x2, y1 + y2, z1 + z2)).or_insert(0) += v1 * v2;
        }
    }
    out.retain(|_, v| *v != 0);
    out
}

pub fn bloch_matrix4(u: &ZPElem) -> [[LPoly3; 4]; 4] {
    let mut mat: [[LPoly3; 4]; 4] = Default::default();
    for row in 0..4 {
        let (s1, s2, s3) = SIGS[row];
        for (&g, &v) in u {
            let (dx, dy, dz, col) = COSET_PROD[row][g.c];
            let pt = (s1 * g.ix + dx, s2 * g.iy + dy, s3 * g.iz + dz);
            *mat[row][col].entry(pt).or_insert(0) += v;
        }
        for col in 0..4 {
            mat[row][col].retain(|_, v| *v != 0);
        }
    }
    mat
}

fn lp_det3(m: &[[&LPoly3; 3]; 3]) -> LPoly3 {
    let t0 = lp_mul(m[0][0], &lp_sub(&lp_mul(m[1][1], m[2][2]), &lp_mul(m[1][2], m[2][1])));
    let t1 = lp_mul(m[0][1], &lp_sub(&lp_mul(m[1][0], m[2][2]), &lp_mul(m[1][2], m[2][0])));
    let t2 = lp_mul(m[0][2], &lp_sub(&lp_mul(m[1][0], m[2][1]), &lp_mul(m[1][1], m[2][0])));
    lp_add(&lp_sub(&t0, &t1), &t2)
}

pub fn det_bloch4(u: &ZPElem) -> LPoly3 {
    let m = bloch_matrix4(u);
    let c0 = lp_det3(&[[&m[1][1], &m[1][2], &m[1][3]], [&m[2][1], &m[2][2], &m[2][3]], [&m[3][1], &m[3][2], &m[3][3]]]);
    let c1 = lp_det3(&[[&m[1][0], &m[1][2], &m[1][3]], [&m[2][0], &m[2][2], &m[2][3]], [&m[3][0], &m[3][2], &m[3][3]]]);
    let c2 = lp_det3(&[[&m[1][0], &m[1][1], &m[1][3]], [&m[2][0], &m[2][1], &m[2][3]], [&m[3][0], &m[3][1], &m[3][3]]]);
    let c3 = lp_det3(&[[&m[1][0], &m[1][1], &m[1][2]], [&m[2][0], &m[2][1], &m[2][2]], [&m[3][0], &m[3][1], &m[3][2]]]);
    lp_sub(&lp_add(&lp_sub(&lp_mul(&m[0][0], &c0), &lp_mul(&m[0][1], &c1)), &lp_mul(&m[0][2], &c2)), &lp_mul(&m[0][3], &c3))
}

/// Exact signed Haah cubic code `k_logical(L, p)` via 2D quotient elimination over `F_p`.
pub fn signed_haah_k_logical(l: usize, p: i64, a1: i64, a2: i64, a3: i64, b1: i64, b2: i64, b3: i64) -> usize {
    let mul_r = |a: &Vec<i64>, b: &Vec<i64>| -> Vec<i64> {
        let mut c = vec![0i64; l * l];
        for i1 in 0..l {
            for j1 in 0..l {
                let v1 = a[i1 * l + j1];
                if v1 == 0 { continue; }
                for i2 in 0..l {
                    let ri = (i1 + i2) % l;
                    for j2 in 0..l {
                        let v2 = b[i2 * l + j2];
                        if v2 != 0 {
                            let idx = ri * l + ((j1 + j2) % l);
                            c[idx] = (c[idx] + v1 * v2) % p;
                        }
                    }
                }
            }
        }
        c
    };
    let mut zp = vec![0i64; l * l];
    zp[0] = (-a3).rem_euclid(p);
    zp[(1 % l) * l] = (zp[(1 % l) * l] - a3 * a1).rem_euclid(p);
    zp[1 % l] = (zp[1 % l] - a3 * a2).rem_euclid(p);

    let mut res = vec![0i64; l * l];
    res[0] = 1;
    let mut base = zp;
    let mut e = l;
    while e > 0 {
        if e & 1 == 1 { res = mul_r(&res, &base); }
        base = mul_r(&base, &base);
        e >>= 1;
    }
    res[0] = (res[0] - 1).rem_euclid(p);

    let mut h1 = vec![0i64; l * l];
    let terms = [
        (2, 0, -a1 * b3),
        (1, 1, a3 * b1 - a2 * b3 - a1 * b2),
        (0, 2, -a2 * b2),
        (1, 0, -b3),
        (0, 1, -b2),
        (0, 0, a3),
    ];
    for (i, j, c) in terms {
        let idx = (i % l) * l + (j % l);
        h1[idx] = (h1[idx] + c).rem_euclid(p);
    }

    let n2 = l * l;
    let mut mat: Vec<Vec<i64>> = Vec::with_capacity(2 * n2);
    for poly in [&h1, &res] {
        let nz: Vec<(usize, usize, i64)> = (0..l)
            .flat_map(|a| (0..l).filter_map(move |b| {
                let v = poly[a * l + b];
                if v != 0 { Some((a, b, v)) } else { None }
            }))
            .collect();
        for i in 0..l {
            for j in 0..l {
                let mut row = vec![0i64; n2];
                for &(a, b, v) in &nz {
                    row[((i + a) % l) * l + ((j + b) % l)] = v;
                }
                mat.push(row);
            }
        }
    }
    let rk = rank_mod_p(&mut mat, p);
    2 * (n2 - rk)
}

fn mod_pow(mut base: i64, mut exp: i64, p: i64) -> i64 {
    let mut acc = 1i64;
    base = base.rem_euclid(p);
    while exp > 0 {
        if exp & 1 == 1 { acc = (acc * base) % p; }
        base = (base * base) % p;
        exp >>= 1;
    }
    acc
}

fn rank_mod_p(a: &mut [Vec<i64>], p: i64) -> usize {
    let m = a.len();
    if m == 0 { return 0; }
    let n = a[0].len();
    let mut r = 0;
    for c in 0..n {
        let mut piv = None;
        for i in r..m {
            if a[i][c] != 0 { piv = Some(i); break; }
        }
        let Some(pi) = piv else { continue };
        a.swap(r, pi);
        let inv = mod_pow(a[r][c], p - 2, p);
        for j in c..n {
            a[r][j] = (a[r][j] * inv) % p;
        }
        for i in 0..m {
            if i != r && a[i][c] != 0 {
                let fac = a[i][c];
                for j in c..n {
                    let v = a[r][j];
                    a[i][j] = (a[i][j] - fac * v).rem_euclid(p);
                }
            }
        }
        r += 1;
        if r == m { break; }
    }
    r
}

/* --- Complex Arithmetic & 4-Band Non-Hermitian Amoeba / B_4 Braid Tracker --- */

#[derive(Clone, Copy, Debug)]
pub struct C64 { pub re: f64, pub im: f64 }

impl C64 {
    pub const ZERO: C64 = C64 { re: 0.0, im: 0.0 };
    pub const ONE: C64 = C64 { re: 1.0, im: 0.0 };
    pub fn new(re: f64, im: f64) -> Self { Self { re, im } }
    pub fn add(self, o: C64) -> C64 { C64::new(self.re + o.re, self.im + o.im) }
    pub fn sub(self, o: C64) -> C64 { C64::new(self.re - o.re, self.im - o.im) }
    pub fn mul(self, o: C64) -> C64 { C64::new(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re) }
    pub fn div(self, o: C64) -> C64 {
        let d = o.re * o.re + o.im * o.im;
        C64::new((self.re * o.re + self.im * o.im) / d, (self.im * o.re - self.re * o.im) / d)
    }
    pub fn abs(self) -> f64 { self.re.hypot(self.im) }
    pub fn exp(self) -> C64 {
        let r = self.re.exp();
        C64::new(r * self.im.cos(), r * self.im.sin())
    }
}

pub fn eval_bloch_c64(m: &[[LPoly3; 4]; 4], kx: f64, ky: f64, kz: f64, mu: (f64, f64, f64)) -> [[C64; 4]; 4] {
    let mut out = [[C64::ZERO; 4]; 4];
    for i in 0..4 {
        for j in 0..4 {
            let mut s = C64::ZERO;
            for (&(px, py, pz), &v) in &m[i][j] {
                let re = (px as f64) * mu.0 + (py as f64) * mu.1 + (pz as f64) * mu.2;
                let im = (px as f64) * kx + (py as f64) * ky + (pz as f64) * kz;
                let e = C64::new(re, im).exp();
                s = s.add(C64::new(e.re * (v as f64), e.im * (v as f64)));
            }
            out[i][j] = s;
        }
    }
    out
}

pub fn det4_c64(m: &[[C64; 4]; 4]) -> C64 {
    let perms: [([usize; 4], f64); 24] = [
        ([0,1,2,3], 1.0),([0,1,3,2],-1.0),([0,2,1,3],-1.0),([0,2,3,1], 1.0),([0,3,1,2], 1.0),([0,3,2,1],-1.0),
        ([1,0,2,3],-1.0),([1,0,3,2], 1.0),([1,2,0,3], 1.0),([1,2,3,0],-1.0),([1,3,0,2],-1.0),([1,3,2,0], 1.0),
        ([2,0,1,3], 1.0),([2,0,3,1],-1.0),([2,1,0,3],-1.0),([2,1,3,0], 1.0),([2,3,0,1], 1.0),([2,3,1,0],-1.0),
        ([3,0,1,2],-1.0),([3,0,2,1], 1.0),([3,1,0,2], 1.0),([3,1,2,0],-1.0),([3,2,0,1],-1.0),([3,2,1,0], 1.0),
    ];
    let mut tot = C64::ZERO;
    for (p, sgn) in perms {
        let t = m[0][p[0]].mul(m[1][p[1]]).mul(m[2][p[2]]).mul(m[3][p[3]]);
        tot = tot.add(C64::new(t.re * sgn, t.im * sgn));
    }
    tot
}

pub fn ronkin_function(m: &[[LPoly3; 4]; 4], mu: (f64, f64, f64), grid_n: usize) -> f64 {
    let mut sum = 0.0f64;
    let step = 2.0 * PI / (grid_n as f64);
    for ix in 0..grid_n {
        let kx = (ix as f64) * step;
        for iy in 0..grid_n {
            let ky = (iy as f64) * step;
            for iz in 0..grid_n {
                let kz = (iz as f64) * step;
                let d = det4_c64(&eval_bloch_c64(m, kx, ky, kz, mu)).abs();
                sum += d.max(1e-15).ln();
            }
        }
    }
    sum / ((grid_n * grid_n * grid_n) as f64)
}

pub fn spectral_winding(m: &[[LPoly3; 4]; 4], axis: char, f1: f64, f2: f64, e_ref: C64, npts: usize) -> (f64, f64) {
    let mut vals = Vec::with_capacity(npts);
    let mut min_abs = f64::INFINITY;
    for n in 0..npts {
        let t = 2.0 * PI * (n as f64) / (npts as f64);
        let mut mat = match axis {
            'x' => eval_bloch_c64(m, t, f1, f2, (0.0, 0.0, 0.0)),
            'y' => eval_bloch_c64(m, f1, t, f2, (0.0, 0.0, 0.0)),
            _ => eval_bloch_c64(m, f1, f2, t, (0.0, 0.0, 0.0)),
        };
        for i in 0..4 { mat[i][i] = mat[i][i].sub(e_ref); }
        let d = det4_c64(&mat);
        min_abs = min_abs.min(d.abs());
        vals.push(d);
    }
    let mut ang = 0.0;
    for n in 0..npts {
        let ratio = vals[(n + 1) % npts].div(vals[n]);
        ang += ratio.im.atan2(ratio.re);
    }
    (ang / (2.0 * PI), min_abs)
}

fn charpoly4_c64(m: &[[C64; 4]; 4]) -> [C64; 5] {
    let mm = |a: &[[C64; 4]; 4], b: &[[C64; 4]; 4]| -> [[C64; 4]; 4] {
        let mut c = [[C64::ZERO; 4]; 4];
        for i in 0..4 { for j in 0..4 { for k in 0..4 { c[i][j] = c[i][j].add(a[i][k].mul(b[k][j])); } } }
        c
    };
    let tr = |a: &[[C64; 4]; 4]| -> C64 { a[0][0].add(a[1][1]).add(a[2][2]).add(a[3][3]) };
    let scale = |z: C64, f: f64| C64::new(z.re * f, z.im * f);
    let add_diag = |a: &[[C64; 4]; 4], d: C64| -> [[C64; 4]; 4] {
        let mut o = *a;
        for i in 0..4 { o[i][i] = o[i][i].add(d); }
        o
    };
    let c3 = scale(tr(m), -1.0);
    let b1 = add_diag(m, c3);
    let mb1 = mm(m, &b1);
    let c2 = scale(tr(&mb1), -0.5);
    let b2 = add_diag(&mb1, c2);
    let mb2 = mm(m, &b2);
    let c1 = scale(tr(&mb2), -1.0 / 3.0);
    let b3 = add_diag(&mb2, c1);
    let mb3 = mm(m, &b3);
    let c0 = scale(tr(&mb3), -0.25);
    [C64::ONE, c3, c2, c1, c0]
}

pub fn quartic_discriminant_c64(c: &[C64; 5]) -> C64 {
    let b = c[1]; let cc = c[2]; let d = c[3]; let e = c[4];
    let sc = |k: f64, z: C64| C64::new(k * z.re, k * z.im);
    let b2 = b.mul(b); let b3 = b2.mul(b); let b4 = b2.mul(b2);
    let c2 = cc.mul(cc); let c3 = c2.mul(cc); let c4 = c2.mul(c2);
    let d2 = d.mul(d); let d3 = d2.mul(d); let d4 = d2.mul(d2);
    let e2 = e.mul(e); let e3 = e2.mul(e);
    sc(256.0, e3)
        .sub(sc(192.0, b.mul(d).mul(e2)))
        .sub(sc(128.0, c2.mul(e2)))
        .add(sc(144.0, cc.mul(d2).mul(e)))
        .sub(sc(27.0, d4))
        .add(sc(144.0, b2.mul(cc).mul(e2)))
        .sub(sc(6.0, b2.mul(d2).mul(e)))
        .sub(sc(80.0, b.mul(c2).mul(d).mul(e)))
        .add(sc(18.0, b.mul(cc).mul(d3)))
        .add(sc(16.0, c4.mul(e)))
        .sub(sc(4.0, c3.mul(d2)))
        .sub(sc(27.0, b4.mul(e2)))
        .add(sc(18.0, b3.mul(cc).mul(d).mul(e)))
        .sub(sc(4.0, b3.mul(d3)))
        .sub(sc(4.0, b2.mul(c3).mul(e)))
        .add(b2.mul(c2).mul(d2))
}

pub fn discriminant_braid_degree(m: &[[LPoly3; 4]; 4], axis: char, f1: f64, f2: f64, npts: usize) -> (f64, f64) {
    let mut vals = Vec::with_capacity(npts);
    let mut min_abs = f64::INFINITY;
    for n in 0..npts {
        let t = 2.0 * PI * (n as f64) / (npts as f64);
        let mat = match axis {
            'x' => eval_bloch_c64(m, t, f1, f2, (0.0, 0.0, 0.0)),
            'y' => eval_bloch_c64(m, f1, t, f2, (0.0, 0.0, 0.0)),
            _ => eval_bloch_c64(m, f1, f2, t, (0.0, 0.0, 0.0)),
        };
        let disc = quartic_discriminant_c64(&charpoly4_c64(&mat));
        min_abs = min_abs.min(disc.abs());
        vals.push(disc);
    }
    let mut ang = 0.0;
    for n in 0..npts {
        let ratio = vals[(n + 1) % npts].div(vals[n]);
        ang += ratio.im.atan2(ratio.re);
    }
    (ang / (2.0 * PI), min_abs)
}

fn roots4_dk(c: &[C64; 5], init: Option<[C64; 4]>) -> [C64; 4] {
    let mut r = init.unwrap_or_else(|| {
        let mut a = [C64::ZERO; 4];
        for k in 0..4 {
            let th = 2.0 * PI * (k as f64) / 4.0 + 0.13;
            a[k] = C64::new(2.1 * th.cos(), 2.1 * th.sin());
        }
        a
    });
    for _ in 0..80 {
        let mut mx = 0.0f64;
        for i in 0..4 {
            let z = r[i];
            let fz = z.add(c[1]).mul(z).add(c[2]).mul(z).add(c[3]).mul(z).add(c[4]);
            let mut denom = C64::ONE;
            for j in 0..4 {
                if i != j { denom = denom.mul(z.sub(r[j])); }
            }
            if denom.abs() < 1e-18 { denom = C64::new(1e-18, 0.0); }
            let step = fz.div(denom);
            r[i] = r[i].sub(step);
            mx = mx.max(step.abs());
        }
        if mx < 1e-13 { break; }
    }
    r
}

pub fn track_braid_loop(m: &[[LPoly3; 4]; 4], axis: char, f1: f64, f2: f64, nsteps: usize) -> ([usize; 4], f64, i32, Vec<String>) {
    let perms: [[usize; 4]; 24] = [
        [0,1,2,3],[0,1,3,2],[0,2,1,3],[0,2,3,1],[0,3,1,2],[0,3,2,1],
        [1,0,2,3],[1,0,3,2],[1,2,0,3],[1,2,3,0],[1,3,0,2],[1,3,2,0],
        [2,0,1,3],[2,0,3,1],[2,1,0,3],[2,1,3,0],[2,3,0,1],[2,3,1,0],
        [3,0,1,2],[3,0,2,1],[3,1,0,2],[3,1,2,0],[3,2,0,1],[3,2,1,0],
    ];
    let eval_at = |t: f64| match axis {
        'x' => eval_bloch_c64(m, t, f1, f2, (0.0, 0.0, 0.0)),
        'y' => eval_bloch_c64(m, f1, t, f2, (0.0, 0.0, 0.0)),
        _ => eval_bloch_c64(m, f1, f2, t, (0.0, 0.0, 0.0)),
    };
    let r0 = roots4_dk(&charpoly4_c64(&eval_at(0.0)), None);
    let mut r_prev = r0;
    let mut min_gap = f64::INFINITY;
    let mut word: Vec<String> = Vec::new();
    for s in 1..=nsteps {
        let t = 2.0 * PI * (s as f64) / (nsteps as f64);
        let r_curr = roots4_dk(&charpoly4_c64(&eval_at(t)), Some(r_prev));
        let mut best_p = perms[0];
        let mut best_d = f64::INFINITY;
        for p in perms {
            let d = (0..4).map(|i| r_curr[p[i]].sub(r_prev[i]).abs()).sum::<f64>();
            if d < best_d { best_d = d; best_p = p; }
        }
        let r_matched = [r_curr[best_p[0]], r_curr[best_p[1]], r_curr[best_p[2]], r_curr[best_p[3]]];
        for i in 0..4 {
            for j in (i + 1)..4 {
                min_gap = min_gap.min(r_matched[i].sub(r_matched[j]).abs());
            }
        }
        let mut ord_prev: [usize; 4] = [0, 1, 2, 3];
        ord_prev.sort_by(|&a, &b| r_prev[a].re.partial_cmp(&r_prev[b].re).unwrap());
        let mut ord_curr: [usize; 4] = [0, 1, 2, 3];
        ord_curr.sort_by(|&a, &b| r_matched[a].re.partial_cmp(&r_matched[b].re).unwrap());
        if ord_prev != ord_curr {
            let mut arr = ord_prev;
            for idx_target in 0..4 {
                let b = ord_curr[idx_target];
                let mut cur_idx = arr.iter().position(|&x| x == b).unwrap();
                while cur_idx > idx_target {
                    let b_left = arr[cur_idx - 1];
                    let b_right = arr[cur_idx];
                    let im_diff = (r_matched[b_right].im + r_prev[b_right].im) - (r_matched[b_left].im + r_prev[b_left].im);
                    word.push(format!("s{}{}", cur_idx, if im_diff > 0.0 { "+" } else { "-" }));
                    arr.swap(cur_idx - 1, cur_idx);
                    cur_idx -= 1;
                }
            }
        }
        r_prev = r_matched;
    }
    let mut best_p = perms[0];
    let mut best_d = f64::INFINITY;
    for p in perms {
        let d = (0..4).map(|i| r_prev[i].sub(r0[p[i]]).abs()).sum::<f64>();
        if d < best_d { best_d = d; best_p = p; }
    }
    let writhe: i32 = word.iter().map(|w| if w.ends_with('+') { 1 } else { -1 }).sum();
    (best_p, min_gap, writhe, word)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_promislow_group_and_gardam_unit() {
        let a = gardam_alpha();
        let b = gardam_beta();
        assert_eq!(a.len(), 21);
        assert_eq!(b.len(), 21);
        assert_eq!(zp_mul(&a, &b, Some(2)), zp_one());
        assert_eq!(zp_mul(&b, &a, Some(2)), zp_one());
    }

    #[test]
    fn test_gardam_det_mod4_and_hensel() {
        let d = det_bloch4(&gardam_alpha());
        assert_eq!(d.len(), 89);
        assert_eq!(*d.get(&(0, 0, 0)).unwrap(), 97);
        let aug: i64 = d.values().sum();
        assert_eq!(aug, 945);
        for (&(i, j, k), &v) in &d {
            if (i, j, k) == (0, 0, 0) {
                assert_eq!((v - 1).rem_euclid(4), 0);
            } else {
                assert_eq!(v.rem_euclid(4), 0);
            }
            assert_eq!(d.get(&(i, -j, -k)), Some(&v));
            assert_eq!(d.get(&(-i, j, -k)), Some(&v));
            assert_eq!(d.get(&(-i, -j, k)), Some(&v));
        }
        for bits in 1..=6 {
            let (inv, ok) = gardam_hensel_inverse(bits);
            assert!(ok, "Hensel lift failed at 2^{}", bits);
            assert!(inv.len() >= 21);
        }
    }

    #[test]
    fn test_haah_prime_bifurcation_exact() {
        // CC1 (m=0): p=2 -> 6,2,14,2,6,2,30; p=3 -> 6,0,6,0,18; p=5 -> L=10:30
        assert_eq!(signed_haah_k_logical(4, 2, 1,1,1, 1,1,1), 14);
        assert_eq!(signed_haah_k_logical(6, 3, 1,1,1, 1,1,1), 18);
        assert_eq!(signed_haah_k_logical(10, 5, 1,1,1, 1,1,1), 30);
        // Singular-at-p=3 class m=1 (1,1,1, 1,1,-1): L=8 at p=3 jumps to 24!
        assert_eq!(signed_haah_k_logical(8, 3, 1,1,1, 1,1,-1), 24);
        // First odd-L odd-prime witness: p=23, L=11 -> k = 6 > 0!
        assert!(signed_haah_k_logical(11, 23, 1,1,1, 1,1,1) > 0);
    }

    #[test]
    fn test_v4_bipolar_winding_antisymmetry_and_s4_braids() {
        let m = bloch_matrix4(&gardam_alpha());
        let (w_pos, g1) = spectral_winding(&m, 'x', 1.2, 2.1, C64::ZERO, 512);
        let (w_neg, g2) = spectral_winding(&m, 'x', 1.2, -2.1, C64::ZERO, 512);
        assert!(g1 > 1.0 && g2 > 1.0);
        assert!((w_pos + w_neg).abs() < 1e-6, "V4 bipolar cancellation failed: {} vs {}", w_pos, w_neg);

        let r0 = ronkin_function(&m, (0.0, 0.0, 0.0), 10);
        let rx = ronkin_function(&m, (0.5, 0.0, 0.0), 10);
        let rmx = ronkin_function(&m, (-0.5, 0.0, 0.0), 10);
        assert!((rx - rmx).abs() < 1e-9);
        assert!(r0 < rx);

        let (p1, gap1, _, _) = track_braid_loop(&m, 'x', 0.3, 0.7, 600);
        let (p2, gap2, _, _) = track_braid_loop(&m, 'x', 1.0, 1.5, 600);
        assert!(gap1 > 0.4 && gap2 > 1.5);
        assert_ne!(p1, [0, 1, 2, 3]);
        assert_ne!(p2, [0, 1, 2, 3]);
    }
}
