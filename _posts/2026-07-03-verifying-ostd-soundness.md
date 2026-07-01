---
layout: post
title: "Proving Soundness for Unsafe Rust: Lessons from a Kernel"
date: 2026-07-03 09:00:00 +0800
author: "Asterinas Team and CertiK"
categories: [formal-verification, rust, kernel]
tags: [unsafe, soundness, verus, ostd, asterinas]
---

*(Foreword: This post summarizes our progress in formally verifying that the trusted unsafe core of the Asterinas OS kernel is sound, tackling a central question in Rust: how do you build a truly trustworthy safe API around unsafe code?)*

Rust's `unsafe` mechanism is an escape hatch for low-level code, and in kernel development, that hatch is unavoidable. Kernels must manage raw physical addresses, manipulate hardware page tables, and execute direct memory access, operations that cannot be expressed as safe Rust. But outside of those low-level operations, the rest of the kernel can still benefit from the high-level guarantees that come for free with safe Rust—if they still hold in the presence of `unsafe`.

The standard way to bridge the gap is to carefully encapsulate the `unsafe` code into a library, allowing the caller to abstract away the implementation details. But an abstraction is only as good as your confidence in it. How can you actually *trust* that the safe API built around your `unsafe` code is perfectly sound for every possible caller, in every possible state? Is it sufficient to dot the code with '`SAFETY: ...`' comments explaining why each use of `unsafe` will not go wrong? No. Even when such comments are detailed and precise, they cannot possibly exhaustively cover the space of possible states that the library as a whole could reach.

<img src="/assets/images/verifying-ostd-soundness/tootsie_pop.png" alt="Tootsie Pop Model" style="max-width: 800px; width: 100%; height: auto;">

**[Asterinas](https://github.com/asterinas/asterinas)** exemplifies the importance of sound encapsulation. Its **[framekernel architecture](https://asterinas.github.io/book/kernel/the-framekernel-architecture.html)** isolates the raw dangerous primitives—physical memory management, synchronization, hardware configuration, and so on—from the rest of the kernel, in the Operating System Standard Library ([OSTD](https://asterinas.github.io/book/ostd/index.html)). Kernel developers working on top of OSTD have access to the powerful abstractions and guarantees of safe Rust. But those guarantees can only be trusted if the OSTD interface is sound! A bug in OSTD isn't just a localized issue; it compromises the safety guarantees of the entire rest of the kernel.

When a small piece of code has an outsized impact on system reliability, it is the perfect candidate for **formal verification** (FV). FV uses a specialized [logic](https://en.wikipedia.org/wiki/Hoare_logic) to create machine-checked proofs that guarantee the code behaves exactly as intended. While writing these specifications and proofs requires significant upfront effort, the payoff is absolute certainty with zero runtime overhead. And as we will show, that *effort is now far more manageable than it used to be*.

A year ago, *our [Phase I](https://asterinas.github.io/2025/02/13/towards-practical-formal-verification-for-a-general-purpose-os-in-rust.html) groundwork* successfully verified isolated functions within the memory management (`mm`) module in OSTD. While meaningful, these proofs were localized.

**This post marks the completion of Phase II.** Not only have we verified *more* functions' individual behavior, but we have successfully proven that the public memory-management API is **sound**. Read on to discover how we achieve this result, and what it means for API consumers.

## Methodology of the Verification

First, let's start with a simple explanation of how verification works. To summarize: formal verification involves annotating program code with a mathematical specification, then running a verification tool that searches for a proof, often aided by additional annotations provided by the engineer. Specifications relate function inputs to their outputs and side-effects, and compose vertically to define the desired behavior of the entire call stack.

Proving soundness goes a step beyong vertical composition. It also requires horizontal composition: the ability for function calls to be combined in any order without undermining the verification guarantees.

In the remainder of this section, we will introduce our choice of verification tool, Verus, and how it naturally supports vertical composition. Then we will explain how horizontal composition becomes a soundness theorem.

### Verus

Our verification tool of choice is [Verus](https://github.com/verus-lang/verus), which integrates directly with the Rust language. Verus code is Rust code, with additional constructs that allow us to annotate functions with preconditions (boolean formulae that must be true in order to safely call the function) and postconditions (which we would like to prove to hold when the function returns). The Verus compiler converts the pre- and postconditions of each function into a logical representation and searches for a proof that all executions that satisfy the preconditions must, at each function exit, satisfy the postconditions.

For complex verification, Verus also allows us to add *ghost state* that exists only during the verification. Because ghost variables are not compiled into executable code, they have no performance impact. They are only used to instrument the code to make information about the broader system legible to the verifier. For example, Verus' pointer libraries provide a ghost [`PointsTo<T>`](https://verus-lang.github.io/verus/verusdoc/vstd/simple_pptr/struct.PointsTo.html) type which encodes the current state of a piece of raw memory containing an object of type `T`. A `PointsTo` can only be constructed and modified through [*valid pointer operations*](https://verus-lang.github.io/verus/verusdoc/vstd/simple_pptr/struct.PPtr.html#example), so its existence provides the "witness" for Verus that the current state of an object in memory is valid.

We define our own ghost types that track parts of the system state that are invisible to any given function. A page table is a tree of nodes and their entries, so a [`PageTableOwner`](https://asterinas.github.io/vostd/ostd/specs/mm/page_table/struct.PageTableOwner.html) is a tree of [`EntryOwner`](https://asterinas.github.io/vostd/ostd/specs/mm/page_table/node/entry_owners/struct.EntryOwner.html) and [`NodeOwner`](https://asterinas.github.io/vostd/ostd/specs/mm/page_table/node/owners/struct.NodeOwner.html) ghost objects, each describing the current state of a concrete object in the system without the need for executable code to access it.

To take a concrete example from the function `Entry::replace`, which overwrites a page table entry. In non-verified code, the function makes three promises when it calls the unsafe [`write_pte`](https://asterinas.github.io/vostd/ostd/mm/page_table/struct.PageTableGuard.html#method.write_pte):

```rust
// SAFETY:
// 1. The index is within the bounds.
// 2. The new PTE is a valid child whose level matches the 
//    current page table node.
// 3. The ownership of the child is transferred to the page table node.
unsafe { self.node.write_pte(self.idx, self.pte) };
```

In Verus, these promises can be made explicit preconditions of `write_pte` as below, which takes an additional ghost argument of type `NodeOwner`. `Tracked` here is a kind of ghost object that obeys the borrow checker.

<!--
Jekyll cannot render Rust macro with a `>` character, so we use a PNG image instead.

```rust
#[verus_spec(with Tracked(owner): Tracked<&mut NodeOwner<C>>)]
fn write_pte(&mut self, idx: usize, pte: C::E)
    requires
      idx < NR_ENTRIES, // Promise 1
      old(self).inner.inner@.invariants(*old(owner)) // Subsumes 2
    ensures
      owner.inv(), // Used in caller to prove 3
      owner.children.value() == old(owner).children.value().update[idx, pte],
      ...
```
-->

<img src="/assets/images/verifying-ostd-soundness/write_pte_spec.png" alt="write_pte() function specification" style="max-width: 700px; width: 95%; height: auto;">

### Vertical Composition

Now all calls to `write_pte` from anywhere in the verified codebase will have these `requires` conditions checked at compile time. At the same time, `write_pte` has obligations of its own (`ensures`). It maintains a weakened invariant, and sets the value of memory at the designated index to match the parameter.

<img src="/assets/images/verifying-ostd-soundness/write_pte.png" alt="write_pte() function specification" style="max-width: 700px; width: 95%; height: auto;">

In addition, the postconditions of `write_pte` allow its caller `replace` to satisfy its own obligations, and on down the call chain. So, function-level specifications are *vertically composed* as a matter of Verus' fundamental design.

<img src="/assets/images/verifying-ostd-soundness/soundness_correctness.png" alt="Soundness and Correctness" style="max-width: 800px; width: 100%; height: auto;">

Properties of this kind, relating a function's inputs to its outputs in a vertical composition between callers and callees, are commonly called *correctness* properties. Soundness and correctness are deeply intertwined. Even if our goal is not necessarily to prove correctness for the entire system, proving *anything* about higher level functions depends on the correctness of lower level functions. In this case, `Entry::replace` is called by `CursorMut::replace_cur_entry`, which is called by [`CursorMut::map`](https://asterinas.github.io/vostd/ostd/mm/vm_space/struct.CursorMut.html#method.map). The soundness proof for `map` depends on this entire chain of logic. Because lower-level proofs are "consumed" by higher-level ones, we are motivated to make their specifications as precise as possible.

In short, we describe the overall system in terms of logical state, and specify how that state is allowed to change during execution. Then, Verus checks that our specifications hold through mathematical deduction. These individual function specifications, combined across the entire system, must support our ultimate claim of soundness.

What does that mean?

### Defining Soundness As Horizontal Composition

"Soundness" is a contract between a library and its caller. As long as the caller does not exhibit UB, the library will not either. The caller is otherwise allowed to do anything it wants! Even if the caller's behavior is nonsensical, the library needs to respond with a well-defined result. In this case, the caller is assumed to be written in safe Rust, so it will satisfy its end of the bargain by definition.

Let's call the caller $C$, and represent the caller linking with OSTD using the $\bowtie$ symbol, creating a whole program $C \bowtie \mathit{OSTD}$. We can think of the result of executing that program once as *trace* of interactions between the two components: a possibly infinite sequence of state transitions. We write $C \bowtie \mathit{OSTD} \rightsquigarrow t$ to mean that the trace $t$ can be produced by $C$ linked with OSTD.

Without getting into the details of how a trace is constructed, it consists of a potentially infinite sequence of events: calls from $C$ to OSTD, returns from OSTD back to $C$, panics, etc. A trace might encode:

- the program running forever - $\mathbf{infinite}(t)$,
- the program terminating or panicking - $\mathbf{terminates}(t)$,
- the program getting *stuck* - $\mathbf{stuck}(t)$ - which means that the Rust abstract machine has no defined way to continue. In other words, *UB*.

A trace that can be legally To sum up soundness in a single formula:

$$
\forall ~ C ~ t. ~ \textnormal{safe}(C) \wedge C \bowtie \mathit{OSTD} \rightsquigarrow t \Rightarrow \mathbf{well\_defined}(t)
$$

where

$$
\mathbf{well\_defined}(t) \triangleq \mathbf{infinite}(t) \lor \mathbf{terminates}(t)
$$

and

$$
\mathbf{well\_defined}(t) \Rightarrow \neg \mathbf{stuck}(t)
$$

Let's examine the implications of this formulation:

- We quantify over all possible callers, which is much harder than verifying a single program. The only obligation we impose on $C$ is $\mathbf{safe}(C)$: that the caller is well-typed under Rust's type system and contains no `unsafe` blocks.
- We quantify over all traces; **for the kernel develeoper**, this means that they can call any OSTD functions in any order, with any arguments, and be assured of never reaching undefined behavior.
- UB is undecidable, but by definition, a Verus-verified function is well-defined. We aren't looking for individual cases of UB, we are constructively proving that there is some defined behavior for any $C$, which inherently rules out UB.

### Proof by Invariant

The first step to proving the theorem above is breaking down a trace into individual calls. The key is to define a set of invariants for each type defined in OSTD that can be proven to always hold true, and to use them as the sole preconditions for all API functions.

By induction, if the system starts in a valid state, and every possible API call preserves the invariants on objects that it interacts with, then the state is always valid between calls. This allows us to break the verification of a system-level property into a series of *correctness* proofs. The invariants are the glue that hold them together in a *horizontal composition*.

<img src="/assets/images/verifying-ostd-soundness/horizontal.png" alt="Soundness as Horizontal Composition" style="max-width: 800px; width: 100%; height: auto;">

To see this in practice, let's look at selected clauses from `metaregion_sound`, the most critical system invariant in the memory management (`mm`) module. Below is an abbreviated version. This rule is defined on an [`EntryOwner`](https://asterinas.github.io/vostd/ostd/specs/mm/page_table/node/entry_owners/struct.EntryOwner.html#method.metaregion_sound), the abstract ghost state associated with an entry in a page table. It asserts that the associated page table entry matches the global physical memory records ([`MetaRegionOwners`](https://asterinas.github.io/vostd/ostd/specs/mm/frame/meta_region_owners/struct.MetaRegionOwners.html)), which live in a special metadata region.

```rust
impl<C: PageTableConfig> EntryOwner<C> {

    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        let idx = frame_to_index(self.meta_slot_paddr().unwrap());
        if self.is_node() {
            &&& 0 < regions.ref_count(idx) <= REF_COUNT_MAX
            &&& regions.slot_owners[idx].paths_in_pt == set![self.path]
            // Other conditions omitted
        } else if self.is_frame() {
            &&& regions.slot_owners[idx].paths_in_pt.contains(self.path)
            // Other conditions omitted
        } else {
            true
        }
    }

}
```

The [`paths_in_pt`](https://asterinas.github.io/vostd/ostd/specs/mm/frame/meta_owners/struct.MetaSlotOwner.html#structfield.paths_in_pt) clause in the `is_node()` branch ensures that each page table internal **node** corresponds to exactly one position in the tree. The equivalent condition for mapped frames (`.is_frame()`) is weaker, only requiring that the current entry's path be contained in the set, because the same physical frame may legitimately be mapped to multiple virtual addresses simultaneously.

Collectively, system invariants like `metaregion_sound` define the strict rules that every public API must preserve. This is exactly why verifying isolated functions is insufficient. Even if individual functions are completely correct in a vacuum, any unverified code touching the same data structures could silently violate these shared invariants, thus collapsing the entire system's proof. To guarantee true soundness, the module must be verified as a cohesive whole. We check the final soundness property by embedding the specifications of verified functions in a state machine, which may take arbitrary steps using the specification of any function in any order.

## Does the Methodology Scale?

A verification approach is only practical if it can be executed without a massive, multi-year engineering effort. Here is the evidence that our methodology not only works in theory but actually scales in practice.

We began a year ago with a proof of concept, verifying selected properties of individual functions but leaving the bulk of the code unverified. After taking lessons from that phase and scaling up our efforts, in just over a year we have expanded to cover the entire virtual memory subsystem of the memory management (`mm`) module, from raw physical frame allocation at the bottom to virtual address space mapping at the top. Recall that horizontal composition is vital for proving soundness: verifying an entire subsystem is much more valuable than disconnected functions. Meanwhile, a parallel project called [CortenMM](https://dl.acm.org/doi/10.1145/3731569.3764836) has verified the complex concurrent correctness of the page table's fine-grained locking, and has been published in SOSP '25.

As a proxy for cost, historically, formal verification requires about 20 lines of mathematical proof for every 1 line of code (a 1:20 ratio). This immense cost has blocked widespread industrial adoption. **We reduced this ratio to roughly 1:5.** More directly: we verified the soundness of roughly **6,000 lines of complex code in two person-years.**

This efficiency comes from two factors: Verus’ automated SMT solver effortlessly handles routine mathematical obligations in the background, and OSTD’s tightly scoped, modular architecture prevents proof complexity from spiraling out of control.

Advances in AI help us scale even faster. Because proof annotations often follow predictable patterns derived from the system model, AI can be very effective in helping the SMT solver handle proofs that previously would require human guidance. To this end we built **[KVerus](https://arxiv.org/abs/2605.03822)**, an AI-assisted tool that automatically generates a growing fraction of our proofs. Crucially, AI assistance accelerates the writing process but does not alter the trustworthiness of the results. Every single proof generated by KVerus is strictly checked and validated by Verus's mathematical solver. AI frees our engineers to focus on the big picture questions: specifications, system models, and proof strategy.

Another common critique of formal verification is that proofs quickly become outdated as code evolves. Verification projects are usually static, pinned to a particular version of the target software. We began our verification on OSTD v0.15 and are currently tracking v0.16.0, which was a relatively painless transition thanks to our modular invariant structure and KVerus's ability to help repair proofs. Upstream OSTD recently released v0.18.0, and we plan to update the verified version to track it.

## From Promise to Proof

To recap where we stand: we have verified soundness of a significant subset of OSTD, covering virtual memory management libraries from physical frames up to virtual address spaces. The diagram below shows the structure of the verified subset, with unverified `mm` modules to the left and the rest of OSTD to the right. Compare to last year's proof-of-concept: where we had picked out a handful of functions from each module, now we can simply list the modules. In general any function on a call path from the API functions is verified, save a few that are axiomatized as part of the trusted computing base.

Outside of CortenMM we verify the system as a sequential program, with further concurrent verification a future goal. We are currently expanding into verifying the synchronization primitives in `sync`.

<img src="/assets/images/verifying-ostd-soundness/subset.png" alt="Verified Subset of OSTD" style="max-width: 800px; width: 100%; height: auto;">

We verified part of a kernel with this approach, but very little of it is kernel-specific. Any Rust project relying on a complex `unsafe` core faces similar challenges, and can be approached in a similar way:

- **Draw a schematic:** Abstract away implementation details and define ghost types that mimic the logical structure of your system. Define the relationship between the concrete and abstract. Keep it consistent and document it well. Especially if you have AI assistance, consisten patterns and a few examples will accelerate its performance.
- **Anchor the foundation:** Axiomatize mechanisms below the Rust level carefully in terms of how they interact with your abstract model. Use them to verify that low-level functions stay in sync with their specifications.
- **Don't let the roof leak:** Need a strong precondition to verify a function? Not at the API level! Make it an invariant of the relevant ghost type, and prove that every API function preserves it. Don't make assumptions about the caller; constrain the whole system. When every API function is verified to preserve each invariant, with no extraneous preconditions, soundness follows by induction.
- **Fill in the walls:** You can build up from the lowest level, or down from highest. Either way you will need to iterate. When verifying a caller, you will find that your callee needs a stronger postcondition, or a weaker precondition. When you expand an invariant, you will need to revisit the invariant preservation proofs. Specification changes ripple through the entire effort. Keep them incremental and they'll still be manageable.

When you're done, you'll have top-to-bottom proofs encircling your entire library, that no API call can ever put the system into a state from which its behavior is undefined. The developers using your API can forget that unsafe Rust even exists.
