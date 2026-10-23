module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **Distinctness of bounded bit-sources**: two bit-sources both `< 4 ^ n` and unequal must
disagree (via `deltaPair`) at some position strictly below `n`. Unlike `Theorem88d.lean`'s
`eq_of_deltaOf_agree_of_lt_two_pow` (which this directly mirrors), agreement of `deltaPair k`/
`deltaPair k'` on `[0, n)` means agreement of `k.testBit`/`k'.testBit` on *every* bit `< 2 * n` (both
the `2 * i` and `2 * i + 1` readings) — covering all of `testBit`'s bits below the bound `4 ^ n =
2 ^ (2 * n)`, so `Nat.eq_of_testBit_eq` still finishes in one step once every bit position is routed
through `deltaPair.fst_eq_testBit`/`deltaPair.snd_eq_testBit`. -/
theorem eq_of_deltaPair_agree_of_lt_four_pow {n k k' : ℕ} (hk : k < 4 ^ n) (hk' : k' < 4 ^ n)
    (hagree : ∀ i < n, deltaPair k i = deltaPair k' i) : k = k' := by
  apply Nat.eq_of_testBit_eq
  intro l
  rcases Nat.lt_or_ge l (2 * n) with hl | hl
  · rcases Nat.mod_two_eq_zero_or_one l with hmod | hmod
    · have hl2 : l = 2 * (l / 2) := by omega
      have hi : l / 2 < n := by omega
      have heq := congrArg Prod.fst (hagree (l / 2) hi)
      rw [deltaPair.fst_eq_testBit, deltaPair.fst_eq_testBit] at heq
      rwa [hl2]
    · have hl2 : l = 2 * (l / 2) + 1 := by omega
      have hi : l / 2 < n := by omega
      have heq := congrArg Prod.snd (hagree (l / 2) hi)
      rw [deltaPair.snd_eq_testBit, deltaPair.snd_eq_testBit] at heq
      rwa [hl2]
  · have h4n : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    have hile : (2 : ℕ) ^ (2 * n) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    rw [Nat.testBit_lt_two_pow ((h4n ▸ hk).trans_le hile),
      Nat.testBit_lt_two_pow ((h4n ▸ hk').trans_le hile)]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **Contrapositive form**: two distinct bit-sources both `< 4 ^ n` must disagree somewhere below
`n` — the form actually consumed by `(d)(5)(b)`'s I-formula lemmas (ruling out cross-terms from a
*different* bit-source witnessing the same point). -/
theorem exists_deltaPair_ne_of_lt_of_ne {n k k' : ℕ} (hk : k < 4 ^ n) (hk' : k' < 4 ^ n)
    (hne : k ≠ k') : ∃ i < n, deltaPair k i ≠ deltaPair k' i := by
  by_contra hcon
  push Not at hcon
  exact hne (eq_of_deltaPair_agree_of_lt_four_pow hk hk' hcon)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect4

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hD₀nomin : D₀.NoMinimal)

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₀nomin in
/-- **8.12(d)(4)(c)(iv): non-trivial intersection with `P₀.X n`, still classical.** Combines
`(c)(iii)`'s `atomPairG.master_covered_deltaPair` with `P₀.X n ⊆ D₀.master` (`sub_master`) and
`P₀.X n ≠ ∅` (fresh here: `hD₀nomin.mem_ne_empty`, the one place in `(d)(4)(c)`'s whole closure that
needs `NoMinimal` itself, rather than just `SplitSpec'`/`IsPositive`/`DiffClosed` — `(d)(1)`'s
generalized layer deliberately dropped `NoMinimal`, but this specific fact ("every genuine
neighbourhood, not just the master, is non-empty") has no substitute among the weaker hypotheses).
Picks any `z ∈ P₀.X n` (exists by the above), lands it in some covering piece via `(c)(iii)`, and
that piece's `i` is exactly the witness. -/
theorem exists_atomPairG_deltaPair_inter_Xn_ne_empty (n : ℕ) :
    ∃ i < 4 ^ n, (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 ∩ P₀.X n ≠ ∅ := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr (hD₀nomin.mem_ne_empty (P₀.mem_X n))
  have hzmaster : z ∈ D₀.master := D₀.sub_master (P₀.mem_X n) hz
  obtain ⟨i, hi, hzcover⟩ := atomPairG.master_covered_deltaPair D₀ D₁ hD₀pos hD₀diff splitY hySplit
    hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne n z hzmaster
  exact ⟨i, hi, Set.nonempty_iff_ne_empty.mp ⟨z, hzcover, hz⟩⟩

end AtomPairCorrect4

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect4Snd

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hD₁nomin : D₁.NoMinimal)

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₁nomin in
/-- **8.12(d)(4)(d)(iv): non-trivial intersection with `P₁.X n`, still classical, `D₁`-side.** The
`D₁`-side mirror of `(c)(iv)`'s `exists_atomPairG_deltaPair_inter_Xn_ne_empty`: combines `(d)(iii)`'s
`atomPairG.master_covered_deltaPair_snd` with `P₁.X n ⊆ D₁.master` (`sub_master`) and `P₁.X n ≠ ∅`
(fresh `hD₁nomin.mem_ne_empty`, the `D₁`-side analogue of `(c)(iv)`'s one genuinely new hypothesis).
Picks any `z ∈ P₁.X n` (exists by the above), lands it in some covering piece via `(d)(iii)`, and
that piece's `i` is exactly the witness. Note this alone doesn't fix the `bx` bit `YPseqCode`'s fold
also needs — that's resolved only in `(d)(vi)`. -/
theorem exists_atomPairG_deltaPair_inter_Yn_ne_empty (n : ℕ) :
    ∃ i < 4 ^ n, (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 ∩ P₁.X n ≠ ∅ := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr (hD₁nomin.mem_ne_empty (P₁.mem_X n))
  have hzmaster : z ∈ D₁.master := D₁.sub_master (P₁.mem_X n) hz
  obtain ⟨i, hi, hzcover⟩ := atomPairG.master_covered_deltaPair_snd D₀ D₁ hD₀pos hD₀diff splitY
    hySplit hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne n z hzmaster
  exact ⟨i, hi, Set.nonempty_iff_ne_empty.mp ⟨z, hzcover, hz⟩⟩

end AtomPairCorrect4Snd

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

/-- **The depth-`n` `D₀`-side index**, for bit-source `k`. -/
noncomputable def atomPairIdx0 (n k : ℕ) : ℕ :=
  stateIdx0 (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

end AtomPairCode

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

/-- **The depth-`n` `D₁`-side index**, for bit-source `k`. -/
noncomputable def atomPairIdx1 (n k : ℕ) : ℕ :=
  stateIdx1 (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

end AtomPairCode

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

/-- **The `X`-side half-step atom's packed state** at depth `n`, index `i` (`i` playing the role of
a length-`n` prefix of sign-pairs, via its own base-4 digits, matching `(d)(3)(d)`'s `deltaPair`
convention): re-run `xSubStep` on the depth-`n` two-sided state at bit-source `i`, with the
`X`-sub-step's own bit forced to `1` — the `"+"`/`true` branch `XPseq`'s classical definition
(`Exercise812c.lean`) always selects, regardless of what the *paired* direct-refinement of the
`D₀`-side would otherwise do with a different bit. -/
noncomputable def xPseqAtomState (n i : ℕ) : ℕ :=
  xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair 1
    (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i))))

end XPseqCode

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

/-- **The `Y`-side half-step atom's packed state** at depth `n`, index `i`, and free `X`-sub-step
bit `bx`: run `xSubStep` first at bit `bx` (arbitrary — `YPseq`'s classical definition
(`Exercise812c.lean`) unions over *both* `δ' : Fin n → Bool × Bool` and a free `bx : Bool` for
position `n`'s own `X`-sub-step bit, since `yStep`'s own inputs already depend on it), then
`ySubStep` with its own bit forced to `1` (the `"+"`/`true` branch). -/
noncomputable def yPseqAtomState (n i bx : ℕ) : ℕ :=
  ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1
    (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair bx
      (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)))))))

end YPseqCode

end DomainTheory.NeighbourhoodSystems
