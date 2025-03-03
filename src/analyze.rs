use std::collections::HashMap;

use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
pub struct Results {
    patterns: HashMap<u8, HashMap<u32, (u32, u32)>>
}

fn get_pixel(img: &image::RgbImage, x: u32, y: u32) -> u8 {
    let [r, g, b] = img.get_pixel(x, y).0;
    return if r == 0xff && g == 0xff && b == 0xff { 1 } else { 0 };
}

fn read_pattern(img: &image::RgbImage, x: u32, y: u32) -> u8 {
    let (w, h) = (img.width(), img.height());
    let xc = x + w;
    let yc = y + h;
    get_pixel(img, (xc - 1) % w, (yc - 1) % h) << 7
        | get_pixel(img, xc % w, (yc - 1) % h) << 6
        | get_pixel(img, (xc + 1) % w, (yc - 1) % h) << 5
        | get_pixel(img, (xc - 1) % w, yc % h) << 4
        | get_pixel(img, (xc + 1) % w, yc % h) << 3
        | get_pixel(img, (xc - 1) % w, (yc + 1) % h) << 2
        | get_pixel(img, xc % w, (yc + 1) % h) << 1
        | get_pixel(img, (xc + 1) % w, (yc + 1) % h)
}

impl Results {
    fn new() -> Self {
        let mut patterns = HashMap::new();
        for p in 0..=255 {
            patterns.insert(p, HashMap::new());
        }
        Self {
            patterns,
        }
    }
    fn load() -> Self {
        let mut file = std::fs::File::open("data/frames.json").expect("failed to load results");
        serde_json::from_reader(&mut file).expect("failed to deserialize results")
    }
    fn analyze_frame(&mut self, idx: u32) {
        let path = format!("data/frames/{:0>4}.png", idx);
        let img = image::io::Reader::open(path).expect("failed to open frame")
            .decode().expect("failed to decode frame")
            .to_rgb8();
        for x in 0..img.width() {
            for y in 0..img.height() {
                let pat = read_pattern(&img, x, y);
                let occs = self.patterns.get_mut(&pat).expect(&format!("failed to find pattern {}", pat));
                if !occs.get(&idx).is_some() {
                    occs.insert(idx, (x, y));
                }
            }
        }
    }
    fn analyze(&mut self) {
        for idx in 1..=6574 {
            println!("analyzing frame: {}", idx);
            self.analyze_frame(idx);
        }
    }
}

pub fn analyze() {
    let mut res = Results::new();
    res.analyze();
    let mut file = std::fs::File::create("data/frames.json").expect("failed to open output");
    serde_json::to_writer(&mut file, &res).expect("failed to serialize");
}

pub fn frequencies() {
    let res = Results::load();
    let mut occcounts: Vec<(u8, usize)> = res.patterns.iter().map(|(i, x)| (*i, x.len())).collect();
    occcounts.sort_by_key(|(_, x)| *x);
    for (pat, oc) in occcounts {
        println!("{:#04x} {}", pat, oc);
    }
}
