//! Union-find (disjoint-set): path halving + union by rank.
//!
//! A straight port of the spec's `UnionFind` — the rank rule decides
//! which root survives a merge, so canonical-id choice is identical to
//! the Python version (higher rank wins; first argument on a tie).

/// Disjoint-set forest over dense `0..n` ids.
#[derive(Debug, Default)]
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl UnionFind {
    /// Add a new singleton set; return its index.
    pub fn make(&mut self) -> usize {
        let idx = self.parent.len();
        self.parent.push(idx);
        self.rank.push(0);
        idx
    }

    /// The canonical root of `x` (path halving).
    pub fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    /// Non-compressing root lookup for `&self` contexts.
    pub fn find_ref(&self, mut x: usize) -> usize {
        while self.parent[x] != x {
            x = self.parent[x];
        }
        x
    }

    /// Merge the sets of `a` and `b`; `true` if they differed.
    ///
    /// Union by rank: the higher-rank root survives; equal ranks keep
    /// `a`'s root and bump it — the spec's rule verbatim, so canonical
    /// ids land identically.
    pub fn union(&mut self, a: usize, b: usize) -> bool {
        let mut ra = self.find(a);
        let mut rb = self.find(b);
        if ra == rb {
            return false;
        }
        if self.rank[ra] < self.rank[rb] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[rb] = ra;
        if self.rank[ra] == self.rank[rb] {
            self.rank[ra] += 1;
        }
        true
    }

    /// Number of sets ever created (includes merged-away roots).
    pub fn len(&self) -> usize {
        self.parent.len()
    }

    /// Whether the forest is empty.
    pub fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }
}
