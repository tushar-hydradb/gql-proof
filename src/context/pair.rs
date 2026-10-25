//! Two rules over one tree: `B` runs under `A`, on `A`'s slots.
//!
//! `A` owns the variables: it says which slots meet and how they link. `B` adds no slots of
//! its own; it keeps whatever it needs per slot of `A`'s label (types: a class per variable)
//! and sees, on every step, `A`'s inputs, its output and the link between them, so it can
//! carry its entries along. A step of the pair is a step of `A` followed by each of `B`'s
//! labels for it: `B` can reject or fan out, never relink.

use super::{Context, FactSpec, Link, Masks, Projection, Slot};
use crate::refine::Node;
use std::fmt::Debug;

/// One step of `A` as `B` sees it: `A`'s labels before, and the label and link it made.
pub struct Step<'a, L> {
    pub partial: &'a L,
    pub child: Option<&'a L>,
    pub out: &'a L,
    pub link: &'a Link,
}

/// A rule that runs under `A` and holds no slots of its own.
pub trait Under<A: Context>: Sync {
    type Label: Clone + Ord + Debug + Send + Sync;
    fn name(&self) -> &str;
    /// The partial label of `node` before its first child, given `A`'s.
    fn empty(&self, node: &Node, a: &A::Label) -> Self::Label;
    /// The partial labels after the child at `pos`. Empty rejects.
    fn push(
        &self,
        node: &Node,
        pos: usize,
        partial: &Self::Label,
        child: Option<&Self::Label>,
        a: Step<'_, A::Label>,
    ) -> Vec<Self::Label>;
    /// The labels of `node` from its complete partial label. Empty rejects.
    fn finish(&self, node: &Node, partial: &Self::Label, a: Step<'_, A::Label>)
    -> Vec<Self::Label>;
    fn top(&self, a: &A::Label, label: &Self::Label) -> bool;
    fn show(&self, label: &Self::Label) -> String;
    /// Facts, on bits `A` does not use: both rules see the same masks.
    fn facts(&self) -> Vec<FactSpec> {
        Vec::new()
    }
    /// `label` with dead facts dropped, after `A` projected its own label to `a` (with
    /// `moved` set when `A` replaced it, and where its slots went). `None` rejects.
    fn project(
        &self,
        _a: &A::Label,
        _moved: Option<&Link>,
        label: &Self::Label,
        _masks: Masks,
    ) -> Option<Self::Label> {
        Some(label.clone())
    }
    /// Labels under one label of `A` that may join share a key; `None` never joins.
    fn join_key(&self, _a: &A::Label, _label: &Self::Label) -> Option<Self::Label> {
        None
    }
    /// As [`Context::join`], for two labels under the same label of `A`.
    fn join(&self, _a: &A::Label, _x: &Self::Label, _y: &Self::Label) -> Option<Self::Label> {
        None
    }
    /// As [`Context::grounds`].
    fn grounds(&self, _a: &A::Label, label: &Self::Label) -> Vec<Self::Label> {
        vec![label.clone()]
    }
    /// As [`Context::within`], under one label of `A`.
    fn within(&self, _a: &A::Label, x: &Self::Label, y: &Self::Label) -> bool {
        x == y
    }
    /// As [`Context::overlaps`], under one label of `A`.
    fn overlaps(&self, a: &A::Label, x: &Self::Label, y: &Self::Label) -> bool {
        self.within(a, x, y) || self.within(a, y, x)
    }
    /// As [`Context::partial_key`].
    fn partial_key(&self, _node: &Node, _pos: usize, _partial: &Self::Label) -> u32 {
        0
    }
    /// As [`Context::child_key`].
    fn child_key(&self, _node: &Node, _pos: usize, _child: &Self::Label) -> u32 {
        0
    }
    /// As [`Context::compatible`].
    fn compatible(&self, _node: &Node, _pos: usize, _partial: u32, _child: u32) -> bool {
        true
    }
    /// As [`Context::narrower`], on `B`'s part; the slots are `A`'s.
    fn narrower(
        &self,
        _partial: &Self::Label,
        _map: &[Option<Slot>],
        _target: &Self::Label,
    ) -> bool {
        false
    }
}

/// `A` and `B` together, as one [`Context`].
pub struct Typed<A, B> {
    pub a: A,
    pub b: B,
    name: String,
}

impl<A: Context, B: Under<A>> Typed<A, B> {
    pub fn new(a: A, b: B) -> Self {
        let name = format!("{} with {}", a.name(), b.name());
        Typed { a, b, name }
    }
}

impl<A: Context, B: Under<A>> Context for Typed<A, B> {
    type Label = (A::Label, B::Label);

    fn name(&self) -> &str {
        &self.name
    }

    fn slots(&self, (a, _): &Self::Label) -> usize {
        self.a.slots(a)
    }

    fn empty(&self, node: &Node) -> Self::Label {
        let a = self.a.empty(node);
        let b = self.b.empty(node, &a);
        (a, b)
    }

    fn push(
        &self,
        node: &Node,
        pos: usize,
        (pa, pb): &Self::Label,
        child: Option<&Self::Label>,
    ) -> Vec<(Self::Label, Link)> {
        let (ca, cb) = child.map(|(a, b)| (a, b)).unzip();
        let mut out = Vec::new();
        for (a, link) in self.a.push(node, pos, pa, ca) {
            let step = || Step {
                partial: pa,
                child: ca,
                out: &a,
                link: &link,
            };
            for b in self.b.push(node, pos, pb, cb, step()) {
                out.push(((a.clone(), b), link.clone()));
            }
        }
        out
    }

    fn finish(&self, node: &Node, (pa, pb): &Self::Label) -> Vec<(Self::Label, Link)> {
        let mut out = Vec::new();
        for (a, link) in self.a.finish(node, pa) {
            let step = Step {
                partial: pa,
                child: None,
                out: &a,
                link: &link,
            };
            for b in self.b.finish(node, pb, step) {
                out.push(((a.clone(), b), link.clone()));
            }
        }
        out
    }

    fn top(&self, (a, b): &Self::Label) -> bool {
        self.a.top(a) && self.b.top(a, b)
    }

    fn spells(&self, def: &str, (a, _): &Self::Label) -> bool {
        self.a.spells(def, a)
    }

    fn show(&self, (a, b): &Self::Label) -> String {
        let b = self.b.show(b);
        if b.is_empty() {
            self.a.show(a)
        } else {
            format!("{}:{b}", self.a.show(a))
        }
    }

    fn facts(&self) -> Vec<FactSpec> {
        let mut facts = self.a.facts();
        facts.extend(self.b.facts());
        facts
    }

    fn project(&self, (a, b): &Self::Label, masks: Masks) -> Projection<Self::Label> {
        let (a2, moved) = match self.a.project(a, masks) {
            Projection::Reject => return Projection::Reject,
            Projection::Keep => (a.clone(), None),
            Projection::Replace(a2, link) => (a2, Some(link)),
        };
        let Some(b2) = self.b.project(&a2, moved.as_ref(), b, masks) else {
            return Projection::Reject;
        };
        match moved {
            Some(link) => Projection::Replace((a2, b2), link),
            None if b2 == *b => Projection::Keep,
            None => {
                let same = Link((0..self.a.slots(&a2) as u8).map(Some).collect());
                Projection::Replace((a2, b2), same)
            }
        }
    }

    /// Only `B` joins, under one label of `A`: `A`'s variables and links are the same for both.
    fn join_key(&self, (a, b): &Self::Label) -> Option<Self::Label> {
        Some((a.clone(), self.b.join_key(a, b)?))
    }

    fn join(&self, (a, x): &Self::Label, (a2, y): &Self::Label) -> Option<Self::Label> {
        if a != a2 {
            return None;
        }
        Some((a.clone(), self.b.join(a, x, y)?))
    }

    fn grounds(&self, (a, b): &Self::Label) -> Vec<Self::Label> {
        self.b
            .grounds(a, b)
            .into_iter()
            .map(|g| (a.clone(), g))
            .collect()
    }

    fn within(&self, (a, x): &Self::Label, (a2, y): &Self::Label) -> bool {
        a == a2 && self.b.within(a, x, y)
    }

    fn overlaps(&self, (a, x): &Self::Label, (a2, y): &Self::Label) -> bool {
        a == a2 && self.b.overlaps(a, x, y)
    }

    /// `A`'s key in the high half, `B`'s in the low; compatible when both are.
    fn partial_key(&self, node: &Node, pos: usize, (a, b): &Self::Label) -> u64 {
        (self.a.partial_key(node, pos, a) << 32) | self.b.partial_key(node, pos, b) as u64
    }

    fn child_key(&self, node: &Node, pos: usize, (a, b): &Self::Label) -> u64 {
        (self.a.child_key(node, pos, a) << 32) | self.b.child_key(node, pos, b) as u64
    }

    fn compatible(&self, node: &Node, pos: usize, partial: u64, child: u64) -> bool {
        self.a.compatible(node, pos, partial >> 32, child >> 32)
            && self.b.compatible(node, pos, partial as u32, child as u32)
    }

    fn narrower(&self, (_, p): &Self::Label, map: &[Option<Slot>], (_, t): &Self::Label) -> bool {
        self.b.narrower(p, map, t)
    }
}

/// Nothing under `A`: the pair behaves exactly as `A` alone. What the combinator costs.
pub struct Unit;

impl<A: Context> Under<A> for Unit {
    type Label = ();

    fn name(&self) -> &str {
        "nothing"
    }

    fn empty(&self, _: &Node, _: &A::Label) {}

    fn push(&self, _: &Node, _: usize, _: &(), _: Option<&()>, _: Step<'_, A::Label>) -> Vec<()> {
        vec![()]
    }

    fn finish(&self, _: &Node, _: &(), _: Step<'_, A::Label>) -> Vec<()> {
        vec![()]
    }

    fn top(&self, _: &A::Label, _: &()) -> bool {
        true
    }

    fn show(&self, _: &()) -> String {
        String::new()
    }
}
