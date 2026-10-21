/-ai
The certificate step reads a pair of a combined code and a memo table. The combined code splits into an index and a certificate, and the certificate splits into an output index, a witness, and left and right child certificates. When the index is zero, the result pairs the master guard on the output and the master index with the output. When the index is positive and odd, the result pairs the leaf guard on the witness, half the index, and the output with the output. When the index is positive and even, the two children are read from the memo table at the positions of their codes, and the result pairs the product of their success bits with the node guard on the witness, their outputs, and the output, together with the output.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)

/-- **The certificate step.** Input `p = ⟨w, tbl⟩` with `w = ⟨n, cert⟩` and `tbl` the memo table.
`cert` decodes to `⟨out, wit, lcert, rcert⟩`. Returns `⟨okBit, out⟩`:
* `n = 0`   : `okBit = fe⟨out, mIdx⟩` (is `Q_out = Δ_E`?);
* `n = 2a+1`: `okBit = fU⟨wit, ⟨a, out⟩⟩` (does `wit` witness `X_a u Q_out`?);
* `n = 2a+2`: read children `⟨a.1, lcert⟩`, `⟨a.2, rcert⟩` from `tbl`; `okBit = okL·okR·
  fV⟨wit, ⟨⟨outL, outR⟩, out⟩⟩`. -/
def gStep (p : ℕ) : ℕ :=
  let w := p.unpair.1
  let tbl := p.unpair.2
  let nn := w.unpair.1
  let cert := w.unpair.2
  let out := cert.unpair.1
  let wit := cert.unpair.2.unpair.1
  let lcert := cert.unpair.2.unpair.2.unpair.1
  let rcert := cert.unpair.2.unpair.2.unpair.2
  let b := nn / 2 - 1
  let childL := listGet tbl (w - 1 - Nat.pair b.unpair.1 lcert)
  let childR := listGet tbl (w - 1 - Nat.pair b.unpair.2 rcert)
  selectFn (1 - nn)
    (Nat.pair (fe (Nat.pair out mIdx)) out)
    (selectFn (nn % 2)
      (Nat.pair (fU (Nat.pair wit (Nat.pair (nn / 2) out))) out)
      (Nat.pair (childL.unpair.1 * childR.unpair.1
          * fV (Nat.pair wit (Nat.pair (Nat.pair childL.unpair.2 childR.unpair.2) out))) out))

end Computability

end Exercise717

end DomainTheory.NeighbourhoodSystems
