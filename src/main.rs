#![feature(i128_type)]

extern crate day10;
extern crate day12;

use day10::knot_hash;
use day12::*;


fn main() {
    let key = std::env::args().nth(1).unwrap_or("flqrgnkx".to_string());

    let result = puzzle(&key);
    println!("Result = {}", result);

    let disk = Disk::from_code(&key);
    let sets: Sets = disk.get_topology_str().parse::<Configurations>().unwrap().into();

    println!("Clusters = {}", sets.roots().len());
}

trait Ones {
    fn ones(&self) -> u32;
}

trait One {
    fn one(&self, pos: usize) -> bool;
}

fn ones(n: u8) -> u32 {
    (0..8).map(|s| ((n >> s) % 2) as u32).sum()
}

impl Ones for u8 {
    fn ones(&self) -> u32 {
        ones(*self)
    }
}

impl<T> Ones for [T]
    where T: Ones
{
    fn ones(&self) -> u32 {
        self.iter().map(|n| n.ones()).sum()
    }
}

const HASH_SIZE: usize = 128;

struct Disk {
    hashes: [u128; HASH_SIZE]
}

impl Disk {
    pub fn from_code(code: &str) -> Self {
        let mut hashes = [0; HASH_SIZE];

        for i in 0..HASH_SIZE {
            hashes[i] = as_u128(&knot_hash(&format!("{}-{}", code, i)))
        }
        Self {
            hashes
        }
    }



    fn neighbour(&self, row: usize, col: usize) -> Vec<(usize, usize)> {
        if !self[(row, col)] {
            return vec![];
        }

        fn lower_b(v: usize) -> usize { if v > 0 { v - 1 } else { v } }
        fn upper_b(v: usize) -> usize { if v < (HASH_SIZE - 1) { v + 2 } else { v + 1 } }

        let rows = lower_b(row)..upper_b(row);
        rows.map(|i| (i, col)).chain(
            (lower_b(col)..upper_b(col)).map(|j| (row, j)).
                filter(|&coord| coord != (row, col))
        )
            .filter(|&(r, c)| self[(r, c)])
            .collect()
    }

    fn topology_coord(row: usize, col: usize) -> usize {
        (row << 16) | col
    }

    fn topology_line(&self, row: usize, col: usize) -> String {
        let id = Self::topology_coord(row, col);
        let linked = self.neighbour(row, col)
            .into_iter()
            .map(|(r, c)| format!("{}", Self::topology_coord(r, c)))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} <-> {}", id, linked)
    }

    fn get_topology_str(&self) -> String {
        (0..HASH_SIZE).flat_map(|r|
            (0..HASH_SIZE).map(move |c| (r, c))
        ).filter(|&coord| self[coord])
            .map(|(row, col)| self.topology_line(row, col))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl std::ops::Index<(usize, usize)> for Disk {
    type Output = bool;

    fn index(&self, index: (usize, usize)) -> &Self::Output {
        let (row, col) = index;
        match self.hashes[row].one(col) {
            true => &true,
            false => &false
        }
    }
}

fn puzzle(s: &str) -> u32 {
    (0..128).map(|i| knot_hash(&format!("{}-{}", s, i)).ones()).sum()
}

impl One for u128 {
    fn one(&self, pos: usize) -> bool {
        ((self >> (127 - pos)) % 2) == 1
    }
}

fn as_u128(hash: &[u8]) -> u128 {
    (0..16).fold(0, |r: u128, i| r | (hash[i] as u128) << (8 * (15 - i)))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn count_ones_in_u8() {
        assert_eq!(0, ones(0));
        assert_eq!(1, ones(1));
        assert_eq!(2, ones(6));
        assert_eq!(8, ones(255));
        assert_eq!(2, 6.ones());
    }

    #[test]
    fn count_ones_in_array() {
        assert_eq!(12, [2, 6, 255, 0, 1].ones());
    }

    #[test]
    fn count_ones_in_hash() {
        assert_eq!(4, knot_hash("flqrgnkx-0")[0..1].ones());
        assert_eq!(4, knot_hash("flqrgnkx-1")[0..1].ones());
        assert_eq!(2, knot_hash("flqrgnkx-2")[0..1].ones())
    }

    #[test]
    fn test_puzzle() {
        assert_eq!(8108, puzzle("flqrgnkx"));
    }

    #[test]
    fn test_as_u128() {
        assert_eq!(0, as_u128(&[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]));
        assert_eq!(0xaabf000000000000000000001500001a,
                   as_u128(&[0xaa, 0xbf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x15, 0, 0, 0x1a]));
    }

    #[test]
    fn test_one() {
        let h = 0xa5bf000000000000000000001500001au128;

        assert!(h.one(0));
        assert!(!h.one(1));
        assert!(h.one(2));
        assert!(!h.one(3));
        assert!(!h.one(4));
        assert!(h.one(5));
        assert!(!h.one(6));
        assert!(h.one(7));
    }

    static CODE: &'static str = "flqrgnkx";

    #[test]
    fn build_disc() {
        let disk = Disk::from_code(CODE);

        assert!(disk[(0, 0)]);
        assert!(disk[(1, 1)]);
        assert!(!disk[(0, 2)]);
        assert!(disk[(0, 1)]);
    }

    #[test]
    fn neighbour_of_empty_sector() {
        let disk = Disk::from_code(CODE);

        assert_eq!(Vec::<(usize, usize)>::new(), disk.neighbour(0, 2));
    }

    #[test]
    fn neighbour() {
        let disk = Disk::from_code(CODE);

        assert_eq!(vec![(2, 4), (3, 4), (4, 4), (3, 5)], disk.neighbour(3, 4));
    }

    #[test]
    fn neighbour_boundary() {
        let disk = Disk::from_code(CODE);

        assert_eq!(vec![(0, 0), (0, 1)], disk.neighbour(0, 0));
    }

    #[test]
    fn integration() {
        let disk = Disk::from_code(CODE);

        let sets: Sets = disk.get_topology_str().parse::<Configurations>().unwrap().into();

        assert_eq!(1242, sets.roots().len())

    }
}
