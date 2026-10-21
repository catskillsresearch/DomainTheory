/-ai
The code of a singleton list is a primitive recursive function of its entry.

It equals the successor of the pairing of that entry with zero, because the code of the empty list is zero, and pairing with a constant followed by successor is primitive recursive.

An element of the reconstructed subsystem domain is computable for its presentation if and only if the set of presentation indices whose neighbourhoods lie in the corresponding subsystem is recursively enumerable.

Membership in the enumerated neighbourhood of a code is equivalent to every decoded index lying in that set. In one direction the computable predicate is transported along this equivalence and reindexed by the primitive recursive singleton code, using that decoding a singleton code recovers its entry. In the other direction the recursively enumerable predicate of universal membership over decoded lists is transported back along the same equivalence.

Such an element is computable if and only if that index set is the range of a primitive recursive function.

Rewrite the claim by the previous equivalence. If the index set is recursively enumerable, the master index belongs to it, because the neighbourhood named by the master index is the master neighbourhood of the subsystem, and a recursively enumerable predicate containing a known point is the range of a primitive recursive function. Conversely, the range of a primitive recursive function is recursively enumerable and agrees with the index set by the stated specification.

Folding the universal intersection, from an index that already names a neighbourhood of the subsystem and along a list of such indices, still names a neighbourhood of the subsystem.

The empty list leaves the accumulator. For a longer list, the dichotomy of the universal intersection either returns the master neighbourhood, which belongs to the subsystem, or returns the intersection of the two neighbourhoods. In that case the witnessing finite systems are appended, the element is closed under intersection of neighbourhoods, and the partial meet of the appended list is the intersection of the two partial meets. The inductive hypothesis then continues along the tail.

Every value of the list-indexed enumeration is a neighbourhood of the subsystem.

After rewriting the enumeration as the universal neighbourhood of the fold of the universal intersection along the image of the decoded list, the fold lemma applies. The master index names the master neighbourhood, and each image entry belongs to the subsystem because the range specification supplies the index itself as a witness.

If an element of the reconstructed domain of the universal domain is computable, the corresponding subsystem is effectively given.

The computability criterion supplies a primitive recursive enumerator of its index set, and the term-algebra presentation built from that enumerator is a computable presentation of the subsystem.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.combineSub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.ofSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.subsystemIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubDX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.idxCharAt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubDPresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QstepFn
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'Xcode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.leafCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.masterCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QLookup
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.listToTreeAux
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'xPresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.master_mem_finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_sub_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_sub_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.principal_mem_finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.combineSub_sublist
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_combineSub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_combineSub_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGenSys_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_cons_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_le_iff_forall_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_append_le_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.self_mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_antitone
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_eq_of_nbhdGen_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_append_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystem_ofSubsystem_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_ofSubsystem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystem_ofSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.exists_common_witness
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.ofSubsystem_toSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubDX_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubDX_surj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.consUpd_foldl_idx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_idxCharAt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.idxCharAt_eq_idxchain
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGen_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_subset_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubDX_inter_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubDX_masterIdx_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.UX_Uinter_dichotomy
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'X_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.exists_preimage_of_forall_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'x_surj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.unpair_snd_lt_of_unpair_fst_pos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode_fst_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode_snd_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody_local
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_QLookup
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel_fuelTable_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_QFuel2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel_stable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_eq_QFuel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_leaf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_node
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_of_tag0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_of_tag1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_of_tag_ge2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2x_mem_X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_listToTreeAux
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2x_surj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_Q2inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2inter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X_masterIdx_spec

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714.repred_range_primrec
@[expose] public section

/-!
# Exercise 8.15 (Scott 1981, PRG-19) — `{X ∣ X ◁ D}` is effectively presented if `D` is

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VIII.

> **Exercise 8.15.** Give a *direct* proof that the domain `{X ∣ X ◁ D}` is effectively presented
> if `D` is. (Hint: the finite elements of the domain correspond exactly to the finite systems
> `X ◁ D`.) In the case of `D = 𝒰`, show that the computable elements of the domain correspond
> exactly to the effectively presented domains (up to effective isomorphism).

Scott's `{D' ∣ D' ◁ D}` (ordered by the subsystem relation `◁`, Definition 6.10) is already known to
*be* a domain: Proposition 6.11 (`Proposition611.subsystemReprIso`) exhibits it as order-isomorphic to
`|reprSystem (subFam D) …|`, via the **abstract, `Classical.choice`-laden** representation theorem of
Exercise 2.22. Scott explicitly asks here for a *direct* proof of effective presentability, and the
hint ("finite elements ↔ finite systems `X ◁ D`") points at a concrete, `ℕ`-indexed reconstruction
instead — reusing `Theorem75.lean`'s `interFrom`/`idxchain`/`bitSelect`/`decodeList` toolkit (built
there for exactly this kind of "finite consistent sub-selection" bookkeeping).

## Plan (recorded in `HANDOFF.md` and `arxiv.md`, worked in sequence)

Fix `D : NeighborhoodSystem α` and a `ComputablePresentation P` of `D`.

1. **`Fin(js)`, the finitely generated subsystem** (this file's `finGen`/`finGenSys`): for a finite
   index list `js : List ℕ`, the set of *consistent sub-meets* `Fin(js) := {Y ∣ ∃ sub ⊑ js, D.mem Y ∧
   Y = interFrom P D.master sub}`. This is itself a subsystem `finGenSys(js) ◁ D`, and
   **`Fin_le_iff_forall_mem`**: `Fin(js) ⊆ D'.mem ↔ ∀ i ∈ js, D'.mem (P.X i)` for any `D' ◁ D` — the
   single workhorse lemma for everything downstream (proved by induction on `js`, using
   `interFrom_mem_of_witness` from `Theorem75.lean` to handle "an intermediate partial meet along a
   consistent chain is itself consistent").
2. **The reconstructed system `SubD`** (token type `List ℕ`): neighbourhoods are the anti-monotone
   principal up-sets `nbhd(js) := {js' ∣ Fin(js) ⊆ Fin(js')}`.
3. **The order isomorphism `SubD.Element ≃o {D' ∣ D' ◁ D}`** — fully choice-free, unlike Exercise 2.22.
4. **`ComputablePresentation SubD`** — Scott's two relations reduce to *bounded* quantifiers over
   `bitSelect`-selected sub-lists, decided via `consChain_iff`/`idxchain_spec`/`P.eq_computable`.
5. **Main theorem**: `D.IsEffectivelyGiven → {D' ∣ D' ◁ D}` is (isomorphic to) an effectively given
   domain.
6. (Second half, `D = 𝒰`): deferred pending 1–5.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

/-! ## Subgoal 1 — `Fin(js)`, the finitely generated subsystem -/

section FinGen

variable (P : ComputablePresentation D)


/-! ### `Fin(js)` is a genuine subsystem of `D`. -/

section Combine

variable (js sub1 sub2 : List ℕ)


variable {js sub1 sub2}


end Combine


/-! ### The workhorse lemma: `Fin(js) ⊆ D'.mem ↔ ∀ i ∈ js, D'.mem (P.X i)`. -/


end FinGen

/-! ## Subgoal 2 — the reconstructed system `SubD` -/

section SubD

variable (P : ComputablePresentation D)


end SubD

/-! ## Subgoal 3 — the order isomorphism `SubD.Element ≃o {D' ∣ D' ◁ D}` -/

section OrderIso

variable (P : ComputablePresentation D)


/-! ### Round trip 1: `toSubsystem ∘ ofSubsystem = id` -/


/-! ### Round trip 2: `ofSubsystem ∘ toSubsystem = id` -/


/-! ### The order isomorphism -/


end OrderIso

/-! ## Subgoal 4 — `ComputablePresentation (SubD P)` -/

section Computability

variable (P : ComputablePresentation D)

/-! ### 4a — the enumeration `X n := nbhd(decodeList n)` -/


/-! ### 4b — `idxCharAt`: primitive-recursive extraction of `idxchain (bitSelect L b)`

Reuses `Theorem75.consStp`'s fold (the same one powering `consCharAt`) but projects the *index*
component (`.unpair.2.unpair.1`) instead of the consistency flag (`.unpair.2.unpair.2`). -/


/-! ### 4c — singleton membership: `P.X m ∈ Fin(decodeList c)` is recursively decidable -/


/-! ### 4d — subset decidability: `Fin(decodeList c1) ⊆ Fin(decodeList c2)` -/


/-! ### 4e — `interEq_computable`: `SubDX n ∩ SubDX m = SubDX k` is decidable -/


/-! ### 4f — `cons_computable`/`inter`/`inter_primrec`/`inter_spec` are free -/


/-! ### 4g — `masterIdx`/`masterIdx_spec` -/


/-! ### Assembling `ComputablePresentation (SubD P)` -/


end Computability

/-! ## Subgoal 5 — main theorem: `D.IsEffectivelyGiven → {D' ∣ D' ◁ D}` is (isomorphic to) an
effectively given domain -/

/-! ## Subgoal 6 — second half: computable elements of `SubD P` ↔ effectively presented `D'x`
(relative to `P`'s own enumeration)

See `arxiv.md`'s Exercise 8.15 entry for the plan (6a–6g) and the disjoint-interval example showing
why an *arbitrary* abstract presentation of `D'x` cannot be compared to `P` in general. Everything
below is stated for a general `D`/`P` (the argument never needed `D = 𝒰` specifically); the exercise
instantiates it at `D := U`, `P := UComputablePresentation`. -/

section ComputableElements

variable (P : ComputablePresentation D)

/-! ### 6a — reduce `IsComputableElement` to the index set `{i ∣ D'x.mem (P.X i)}` -/

/-- The singleton-list code `i ↦ encodeList [i]` is primitive recursive. -/
theorem primrec_encodeList_singleton : Nat.Primrec (fun i => encodeList [i]) := by
  have : (fun i => encodeList [i]) = fun i => Nat.pair i 0 + 1 := by
    funext i; show Nat.pair i (encodeList ([] : List ℕ)) + 1 = Nat.pair i 0 + 1
    rw [encodeList]
  rw [this]
  exact Nat.Primrec.succ.comp (Nat.Primrec.pair primrec_id (Nat.Primrec.const 0))

/-- **Subgoal 6a.** `x` is a computable element of `SubD P` iff its "index set relative to `P`" —
the set of `P`-indices `i` with `(toSubsystemSys P x).mem (P.X i)` — is recursively enumerable.
`→`: reindex along `decodeList` (`mem_nbhdGen_iff`) then along the singleton-list code. `←`:
`REPred.forall_mem_decodeList` directly. -/
theorem subsystemU_computable_iff_index_set_re (x : (SubD P).Element) :
    IsComputableElement (SubDPresentation P) x ↔
      REPred (fun i => (toSubsystemSys P x).mem (P.X i)) := by
  have hiff : ∀ n, x.mem (SubDX P n) ↔ ∀ i ∈ decodeList n, (toSubsystemSys P x).mem (P.X i) := by
    intro n; unfold SubDX; exact mem_nbhdGen_iff P x (decodeList n)
  constructor
  · intro hx
    have hx' : REPred (fun n => ∀ i ∈ decodeList n, (toSubsystemSys P x).mem (P.X i)) :=
      REPred.of_iff (fun n => (hiff n).symm) hx
    refine REPred.of_iff (fun i => ?_) (hx'.comp primrec_encodeList_singleton)
    rw [decodeList_encodeList]
    simp only [List.mem_singleton]
    constructor
    · intro h j hj; rw [hj]; exact h
    · intro h; exact h i rfl
  · intro hx
    exact REPred.of_iff hiff hx.forall_mem_decodeList

/-! ### 6b–6d — the main biconditional, via a `P`-relative primitive recursive enumeration -/

/-- **Subgoals 6b–6d, combined.** `x` is a computable element of `SubD P` iff the index set of
`D'x := toSubsystemSys P x` (relative to `P`'s own enumeration) is the range of a primitive
recursive function — Scott's "index set r.e." reduced (Exercise 7.14) to an explicit enumerator.
`→` (6b): `Exercise714.repred_exists_primrec_range`, seeded by the witness `P.masterIdx`
(`D'x.mem (P.X P.masterIdx) = D'x.mem D.master`, always true). `←` (6c):
`Exercise714.repred_range_primrec`. -/
theorem subsystemU_element_computable_iff (x : (SubD P).Element) :
    IsComputableElement (SubDPresentation P) x ↔
      ∃ r : ℕ → ℕ, Nat.Primrec r ∧
        ∀ i, (toSubsystemSys P x).mem (P.X i) ↔ ∃ n, r n = i := by
  rw [subsystemU_computable_iff_index_set_re P x]
  constructor
  · intro hre
    have ha : (toSubsystemSys P x).mem (P.X P.masterIdx) := by
      rw [P.masterIdx_spec]; exact (toSubsystemSys P x).master_mem
    exact Exercise714.repred_exists_primrec_range hre ha
  · rintro ⟨r, hr, hspec⟩
    exact REPred.of_iff hspec (Exercise714.repred_range_primrec hr)

end ComputableElements

/-! ## Subgoal 6e/6f — upgrading to a genuine `ComputablePresentation`, specialized to `D = 𝒰`

Generic `D`/`P` is not enough here: the branch needed to keep `Q'x.X` safe requires an *explicit*
(not merely `RecDecidable`-existentially-known) dichotomy for `P.inter`, which `𝒰`'s canonicalizing
`Uinter` genuinely has (`UX_Uinter_dichotomy`) but an abstract `P` does not. See `HANDOFF.md`'s
2026-07-06 checkpoint for the investigation that led here. -/

section UniversalSubsystem


/-- **The safe-fold invariant.** Folding `Uinter` from a starting point already in `D'x.mem` along a
list all of whose `UX`-images are also in `D'x.mem` stays in `D'x.mem`: `x`'s own *unconditional*
filter closure (`Element.inter_mem`, via `nbhdGen_inter`) combines the two generators' witnessing
index-lists when `Uinter`'s fold genuinely computes an intersection (dichotomy's right disjunct,
using `interFrom_append_eq`), and `D'x.master_mem` handles the fallback (left disjunct). -/
theorem toSubsystemSys_mem_foldl_Uinter (x : (SubD UComputablePresentation).Element) (acc : ℕ)
    (L : List ℕ) (hacc : (toSubsystemSys UComputablePresentation x).mem (UX acc))
    (hL : ∀ i ∈ L, (toSubsystemSys UComputablePresentation x).mem (UX i)) :
    (toSubsystemSys UComputablePresentation x).mem
      (UX (L.foldl (fun a j => Uinter a j) acc)) := by
  induction L generalizing acc with
  | nil => simpa using hacc
  | cons j L' ih =>
    rw [List.forall_mem_cons] at hL
    have hacc' : (toSubsystemSys UComputablePresentation x).mem (UX (Uinter acc j)) := by
      rcases UX_Uinter_dichotomy acc j with hcase | hcase
      · rw [hcase]; exact (toSubsystemSys UComputablePresentation x).master_mem
      · rw [hcase]
        obtain ⟨jsA, hxA, subA, hsubA, hDA, hAeq⟩ := hacc
        obtain ⟨jsJ, hxJ, subJ, hsubJ, hDJ, hJeq⟩ := hL.1
        have hUmem : U.mem (UX acc ∩ UX j) := hcase ▸ U_mem_UX (Uinter acc j)
        refine ⟨jsA ++ jsJ,
          nbhdGen_inter UComputablePresentation jsA jsJ ▸ x.inter_mem hxA hxJ,
          subA ++ subJ, hsubA.append hsubJ, hUmem, ?_⟩
        rw [hAeq, hJeq, interFrom_append_eq UComputablePresentation U.master subA subJ]
    exact ih (Uinter acc j) hacc' hL.2

/-! ### `Q'X` — an explicit enumeration of `D'x`'s neighbourhoods

Given `r` (from `subsystemU_element_computable_iff`, i.e. `x` computable relative to `UP`),
`Q'X r n` folds `Uinter` over the `r`-image of the list coded by `n`, starting from `U`'s master —
reusing the *existing, generic* `Theorem75.idxchain`/`foldCode` machinery (`Recursive.lean`) rather
than reproving fold-primitive-recursiveness from scratch. -/


/-- **`mem_X` for `Q'X r`.** Every `Q'X r n` is a `D'x`-neighbourhood — no consistency hypothesis on
`n` needed, since (a) every entry `r j` of the folded list is *unconditionally* `D'x.mem (UX (r j))`
by `hspec` (taking the trivial witness `j`), and (b) `toSubsystemSys_mem_foldl_Uinter` safely folds
any such list, landing on `D'x.master_mem` if `Uinter`'s dichotomy ever falls back. -/
theorem Q'x_mem_X (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) (n : ℕ) :
    (toSubsystemSys UComputablePresentation x).mem (Q'X r n) := by
  rw [Q'X_eq]
  show (toSubsystemSys UComputablePresentation x).mem
      (UX ((List.map r (decodeList n)).foldl (fun a j => Uinter a j)
        UComputablePresentation.masterIdx))
  apply toSubsystemSys_mem_foldl_Uinter
  · show (toSubsystemSys UComputablePresentation x).mem (UX UmasterIdx)
    rw [UX_UmasterIdx]
    exact (toSubsystemSys UComputablePresentation x).master_mem
  · intro i hi
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    exact (hspec (r j)).mpr ⟨j, rfl⟩


/-! ### The remaining gap: `inter`/`cons_computable` need a term-algebra encoding (resolved below)

`Q'X r` (above) is a fully choice-free, primitive-recursive **enumeration of `D'x`'s neighbourhoods,
onto** (`Q'x_mem_X`, `Q'x_surj`) — the enumeration half of a `ComputablePresentation D'x`. Completing
the *rest* of the structure (`inter`, `inter_spec`, `cons_computable`; `interEq_computable` alone is
fine, a pure reindexing of `U_interEq_computable` along the primitive-recursive `Q'Xcode r`) hits a
**newly-identified obstacle, sharper than the one logged previously**:

The natural candidate `Q'inter r n m := encodeList (decodeList n ++ decodeList m)` — extending `n`'s
list by `m`'s and re-folding — does *not* satisfy `inter_spec`. The reason is that `Uinter`'s
dichotomy fallback is **not "conservative"**: once a fold step falls back to `U.master` (discarding
the true partial intersection), *continuing* the fold from `U.master` can "recover" and compute a
smaller, unrelated value, rather than staying stuck at `U.master`. Concretely: `Q'X r (Q'inter r n
m)`'s value depends on the entries of `n`'s and `m`'s lists *combined sequentially from scratch*, while
`Q'X r n` and `Q'X r m` are each computed *independently* from `U`'s master. If (say) `Q'X r m`'s own
fold happened to fall back internally (its true intersection was empty) while the *globally* combined
fold does not, `Q'X r n ∩ Q'X r m` (inflated by the fallback) and `Q'X r (Q'inter r n m)` (computed
honestly) can be genuinely different sets — even though both individually satisfy `mem_X`. The
alternative fix — `Q'inter r n m := Uinter (Q'Xcode r n) (Q'Xcode r m)` (apply `Uinter` *once more* on
top of the already-computed indices, correct by the existing, unconditional `Uinter_spec`, no
compounding at all) — repairs `inter`/`inter_spec` cleanly, but then breaks `cons_computable`: its
witness `∃k, Q'X r k ⊆ Q'X r n ∩ Q'X r m` needs `k` to be *of the form `Q'Xcode r` applied to some `n,
m`-derived list-code*, and there is no way to name that code without already tracking, as part of
`Q'X`'s own index type, a closed-under-`Uinter`-combination term structure (i.e. re-indexing `Q'X` by
a small term language `{base list, combine n₁ n₂}` via course-of-values recursion, mirroring
`Recursive.lean`'s `tabCode` pattern for a *different* recursively-defined code). Building that term
algebra is genuinely comparable in size to Subgoal 4 itself (as flagged previously), and is **left as
documented future work** — this is a more precise diagnosis of the difficulty than the "extracting a
witness from a `Prop`" issue logged earlier (that issue is avoided entirely by `Q'X`/`Q'Xcode` being
directly-defined functions throughout; the *actual* remaining obstacle is this purely arithmetic
"safe composition of finitely many `Uinter` calls" question). See `HANDOFF.md`'s 2026-07-06 checkpoint.

**Resolution (below): a binary term algebra fixes `inter`/`cons_computable` cleanly.** The fix is to
stop indexing `D'x`'s neighbourhoods by *lists* folded left-to-right through `Uinter` (not
compositional under concatenation, as diagnosed above), and instead index them by a **binary term
algebra** — codes for `leaf j ↦ r j` and `node t1 t2 ↦ Uinter (val t1) (val t2)` — so that combining
two already-built codes is *literally* the `node` constructor, staying inside the index type by
construction (no search needed to name the combined index, unlike the list-code domain). -/

/-! ### The term algebra codes: `leaf j`, `node t1 t2`, `master`

Evaluating a code needs **course-of-values recursion** (a `node`'s two children are only known
`≤` the parent via `Nat.unpair`, not decreasing by a fixed amount), for which we reuse the
*already-built, generic* `fuelTable`/`fuelTable_eq_of_recursion`/`primrec_fuelTable` machinery from
`Recursive.lean` (built there for `decodeFuelOkChar`/`autStateCardFuelChar`) rather than
re-deriving course-of-values primitive recursiveness from scratch. -/

section TermAlgebra


end TermAlgebra

/-! ### `TreeVal r`: evaluating a term-algebra code, via course-of-values fuel recursion -/

section TreeVal

variable (r : ℕ → ℕ)


end TreeVal

/-! ### `Q2X` — the term-algebra-indexed enumeration of `D'x`'s neighbourhoods -/

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)


/-! ### `inter`/`interEq_computable`/`cons_computable` — resolved by the term algebra

The obstacle diagnosed above (`Uinter`'s non-conservative fallback) is fixed by indexing
neighbourhoods by term-algebra codes instead of lists: combining two already-built codes `n`, `m` is
*literally* `nodeCode n m`, no search for a witness code needed, and `Uinter_spec` — applicable
precisely when the consistency hypothesis holds — guarantees the dichotomy's fallback branch of
`UX_Uinter_dichotomy` provably never fires on that witness. -/


/-- **Subgoal 6f, main corollary.** If `x` is a computable element of `SubD UComputablePresentation`,
then `D'x := toSubsystemSys UComputablePresentation x` is effectively given — completing, for
`D = 𝒰`, the second half of Exercise 8.15: computable elements of `SubD UComputablePresentation`
correspond to effectively presented domains, presented *relative to* `UComputablePresentation`'s own
enumeration (see the 6g note in `arxiv.md` for why the fully general "arbitrary presentation"
converse — genuine "uniqueness of computable numberings" — is out of scope). -/
theorem subsystemU_effectivelyGiven_of_isComputableElement
    (hx : IsComputableElement (SubDPresentation UComputablePresentation) x) :
    (toSubsystemSys UComputablePresentation x).IsEffectivelyGiven := by
  obtain ⟨r, hr, hspec⟩ := (subsystemU_element_computable_iff UComputablePresentation x).mp hx
  exact ⟨Q'xPresentation r x hr hspec⟩

/-! ### 6g — scope note: the fully general "arbitrary presentation" converse

`subsystemU_effectivelyGiven_of_isComputableElement` reads Scott's "computable elements correspond
to effectively presented domains (up to effective isomorphism)" via the *specific* presentation
`Q'xPresentation` built **relative to `UComputablePresentation`'s own enumeration** — the natural,
provable reading identified in the Subgoal 6 planning note above (a disjoint-interval example shows
`x.mem (nbhdGen UP js)` does **not** imply `𝒰.mem (interFrom UP 𝒰.master js)` in general, so an
*arbitrary*, unrelated abstract presentation `Q : ComputablePresentation D'x` cannot be compared to
`UP` without extra structure).

The fully general converse Scott's parenthetical "(up to effective isomorphism)" is gesturing at —
that *every* computable presentation of `D'x`, however constructed, is effectively isomorphic to
`Q'xPresentation` — is a genuine "uniqueness of computable numberings" fact (a Rogers-style theorem:
two numberings of the same recursively enumerable structure that both make its structural relations
decidable must be effectively translatable into each other). This is strictly deeper than anything
Definition 7.1's axioms hand us directly, is not needed for the "correspond to" reading already
established by `subsystemU_effectivelyGiven_of_isComputableElement`, and is **deliberately left out
of scope** here. -/
end TreeVal2
end UniversalSubsystem
end DomainTheory.NeighbourhoodSystems
