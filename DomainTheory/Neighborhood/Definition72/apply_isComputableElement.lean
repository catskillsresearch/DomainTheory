/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.Approximable
public import DomainTheory.Neighborhood.Definition72.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}



variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}

/-- **Proposition 7.3 (consequence) (Scott 1981, PRG-19).** "If `f : 𝒟 → ℰ` is computable and
`x ∈ |𝒟|` is computable, then `f(x) ∈ |ℰ|` is also computable." Here `f(x) = {Yₘ ∣ ∃ Xₙ ∈ x, Xₙ f Yₘ}`
(`toElementMap`); surjectivity of `P` lets the witness `X` range over indices `n`, and the resulting
`∃ n, Xₙ ∈ x ∧ Xₙ f Yₘ` is r.e. by `REPred.and`/`REPred.proj`. -/
theorem apply_isComputableElement {P : ComputablePresentation V} {Q : ComputablePresentation W}
    {f : ApproximableMap V W} (hf : IsComputableMap P Q f) {x : V.Element}
    (hx : IsComputableElement P x) : IsComputableElement Q (f.toElementMap x) := by
  have hf' : REPred (fun s => f.rel (P.X s.unpair.1) (Q.X s.unpair.2)) := hf
  have hx' : REPred (fun n => x.mem (P.X n)) := hx
  refine REPred.of_iff (fun m => ?_) ((hx'.comp Nat.Primrec.left).and hf').proj
  simp only [mem_toElementMap, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨X, hX, hfX⟩
    obtain ⟨n, rfl⟩ := P.surj (x.sub hX)
    exact ⟨n, hX, hfX⟩
  · rintro ⟨n, hxn, hfn⟩
    exact ⟨P.X n, hxn, hfn⟩

end DomainTheory.Neighborhood
