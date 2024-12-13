# FreeWillLean: A Formal Proof of the Kochen-Specker Paradox

A formal proof of the Kochen-Specker paradox using Lean 4 and using Mathlib, laying the core mathematical groundwork for Conway and Kochen's Strong Free Will Theorem. This proof demonstrates the mathematical impossibility of predetermined measurement outcomes on certain particles (independent of experiment choices).

## The Kochen-Specker Paradox

The Kochen-Specker paradox can be stated as follows:

It is impossible to color every point on the surface of a unit sphere with one of two colors (red or blue) such that _in any orthogonal triple of points (from the origin), exactly one point is colored red, and two are colored blue_

## Relevance to the Strong Free Will Theorem

Points on a unit sphere correspond to measurement directions on a _spin 1 particle_ (see **References**), and red/blue corresponds to the binary (0/1) outcomes of such measurements. Based on the _SPIN axiom_, measuring a spin 1 particle in 3 mutually orthogonal directions will always 
give (1, 0, 1) in some order. A "classic" deterministic model for particles would assume the results of measurements to be predetermined _independent of the choice of measurement made_. The Kochen-Specker paradox makes this impossible. 
In the words of John Conway and Simon Kochen, the Kochen-Specker paradox implies that "the quantity that is supposedly being measured cannot in fact exist before its measurement."

Using the Kochen-Specker paradox, the Strong Free Will theorem goes on to state that if experimenters have free will in choosing how to orient their measurement devices, then the particles being measured must also exhibit free will in determining their measurement outcomes.

A formalization of the whole Strong Free Will theorem would involve formalizing concepts including inertial frames, temporal causality, etc., which is a challenge for another day:)

## Implementation Details

The proof proceeds by sequentially assigning measurement outcomes to directions _without loss of generality_, building up to a contradiction. In **Basic.lean**, I define the core data structures and lemmas required, including a representation
of the O(3) rotation group to write proofs using WLOG. The main proof is in **KochenSpecker.lean**, where I assign values to measurement directions until a contradiction is reached.

## File Structure

```
├── README.md
├── .gitignore
├── FreeWillLean.lean
├── lake-manifest.json
├── lakefile.lean
├── lean-toolchain
└── FreeWillLean/
    ├── **Basic.lean**            # Core definitions and helper lemmas
    ├── **KochenSpecker.lean**    # Main proof of the paradox
    └── Requirements.lean   
```
## Link
In case you're not already here: github.com/Mr-vedant-gupta/free_will_lean/

## References

Conway, John, and Simon Kochen. "The strong free will theorem." Notices of the AMS 56, no. 2 (2009): 226-232.
