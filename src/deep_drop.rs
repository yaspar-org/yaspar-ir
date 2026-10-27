// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Dropping deep terms and sorts without overflowing the stack.
//!
//! Both ASTs hold their nodes behind reference-counted handles: [`HConsed`] for the typed AST and
//! `Untyped` for the untyped one. Dropping the last handle to a node drops the node, which drops
//! the handles of its children, and so on, so the native stack grows with the depth of the term.
//! A deep enough term then aborts the process with a stack overflow when it is dropped, which is
//! not a panic and cannot be caught.
//!
//! The typed AST also drops nodes when its arena is dropped: the hash-consing table keeps a copy
//! of every node, and each copy holds handles to the node's children.
//!
//! Instead, a node about to be dropped hands its children's handles to a local worklist, emptied
//! in a loop: a handle that is the last one to its node gives the node up ([`TryUnwrap`]), whose
//! children join the worklist, and the node is then dropped without any; any other handle only
//! lowers a count. The stack depth is constant, whatever the depth of the term.
//!
//! The nodes are the payloads of the AST algebra, which both ASTs share, so [`DrainChildren`] is
//! implemented once, on [`alg::Term`](crate::raw::alg::Term) and
//! [`alg::Sort`](crate::raw::alg::Sort); [`instantiate_ast!`](crate::instantiate_ast) implements
//! `Drop` on each AST's node types with [`drop_children`].

use hashconsing::HConsed;

/// A node that can give up the handles of its children instead of dropping them in place
pub trait DrainChildren {
    /// The handle type of the children
    type Child;

    /// Move the handle of every child into `sink`, leaving `self` without children, so that
    /// dropping it does not drop any [`Child`](Self::Child).
    fn drain_children(&mut self, sink: &mut Vec<Self::Child>);
}

/// A handle that gives up its node when it is the last handle to it
pub trait TryUnwrap: Sized {
    /// The node behind the handle
    type Node;

    /// The node, if `self` is the last handle to it; `self` back otherwise.
    fn try_unwrap(self) -> Result<Self::Node, Self>;
}

impl<T> TryUnwrap for HConsed<T> {
    type Node = T;

    fn try_unwrap(self) -> Result<T, Self> {
        HConsed::try_unwrap(self)
    }
}

/// Drop the children of `node` without recursion; call this from the `Drop` of a node.
///
/// The worklist holds handles still to be dropped. A handle that is the last one to its node
/// gives the node up: the node's children join the worklist, and the node is dropped without any,
/// so its own `Drop` returns at once. Any other handle is dropped, which only lowers a count.
pub fn drop_children<H>(node: &mut impl DrainChildren<Child = H>)
where
    H: TryUnwrap,
    H::Node: DrainChildren<Child = H>,
{
    let mut worklist = vec![];
    node.drain_children(&mut worklist);
    while let Some(handle) = worklist.pop() {
        if let Ok(mut child) = handle.try_unwrap() {
            child.drain_children(&mut worklist);
        }
    }
}
