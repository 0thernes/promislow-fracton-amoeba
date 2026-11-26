// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander S. Donahue
//! CLI runner exporting exact verified JSON certificates for promislow-fracton-amoeba.

use promislow_core::*;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("summary");
    match mode {
        "summary" => {
            let a = gardam_alpha();
            let b = gardam_beta();
            let d = det_bloch4(&a);
            let m = bloch_matrix4(&a);
            let r0 = ronkin_function(&m, (0.0, 0.0, 0.0), 16);
            let rx = ronkin_function(&m, (0.5, 0.0, 0.0), 16);
            let rz = ronkin_function(&m, (0.0, 0.0, 0.5), 16);
            let (p1, g1, _, _) = track_braid_loop(&m, 'x', 0.3, 0.7, 600);
            let (d1, _) = discriminant_braid_degree(&m, 'x', 0.3, 0.7, 1024);
            let (p2, g2, _, _) = track_braid_loop(&m, 'x', 1.0, 1.5, 600);
            let (d2, _) = discriminant_braid_degree(&m, 'x', 1.0, 1.5, 1024);
            let (p3, g3, _, _) = track_braid_loop(&m, 'z', 2.0, 1.0, 600);
            let (d3, _) = discriminant_braid_degree(&m, 'z', 2.0, 1.0, 1024);
            let mut hensel_sizes = Vec::new();
            for bits in 1..=6 {
                let (inv, ok) = gardam_hensel_inverse(bits);
                assert!(ok);
                hensel_sizes.push((bits, inv.len()));
            }
            println!("{{");
            println!("  \"gardam_alpha_support\": {},", a.len());
            println!("  \"gardam_beta_support\": {},", b.len());
            println!("  \"det_terms\": {},", d.len());
            println!("  \"det_const_term\": {},", d.get(&(0, 0, 0)).unwrap());
            println!("  \"det_augmentation\": {},", d.values().sum::<i64>());
            println!("  \"ronkin_origin_16\": {:.8},", r0);
            println!("  \"ronkin_mu_x05_16\": {:.8},", rx);
            println!("  \"ronkin_mu_z05_16\": {:.8},", rz);
            println!("  \"braid_x_03_07\": {{\"perm\": {:?}, \"min_gap\": {:.6}, \"disc_braid_deg\": {}}},", p1, g1, d1.round() as i32);
            println!("  \"braid_x_10_15\": {{\"perm\": {:?}, \"min_gap\": {:.6}, \"disc_braid_deg\": {}}},", p2, g2, d2.round() as i32);
            println!("  \"braid_z_20_10\": {{\"perm\": {:?}, \"min_gap\": {:.6}, \"disc_braid_deg\": {}}},", p3, g3, d3.round() as i32);
            let hensel_json: Vec<String> = hensel_sizes
                .iter()
                .map(|(b, s)| format!("[{}, {}]", b, s))
                .collect();
            println!("  \"hensel_2adic_supports\": [{}],", hensel_json.join(", "));
            println!("  \"haah_cc1_p23_L11_k\": {}", signed_haah_k_logical(11, 23, 1, 1, 1, 1, 1, 1));
            println!("}}");
        }
        "haah-table" => {
            println!("{{");
            let primes = [2i64, 3, 5, 7, 11, 13];
            for (pi, &p) in primes.iter().enumerate() {
                let vals: Vec<usize> = (2..=15).map(|l| signed_haah_k_logical(l, p, 1,1,1, 1,1,1)).collect();
                let comma = if pi + 1 < primes.len() { "," } else { "" };
                println!("  \"p{}\": {:?}{}", p, vals, comma);
            }
            println!("}}");
        }
        _ => {
            eprintln!("Usage: promislow_core [summary|haah-table]");
            std::process::exit(1);
        }
    }
}
