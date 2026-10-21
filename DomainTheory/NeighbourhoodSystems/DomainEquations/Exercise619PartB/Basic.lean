/-ai
The token-level master computed by the recursion on a nonempty set equals the master of the construct applied to the one-neighbourhood system on that set.

The proof is by induction on the construct. A constant and the identity are definitionally that master. For a sum or a product both sides are the empty word adjoined to the false-tagged copy of the first component and the true-tagged copy of the second, and the inductive hypotheses rewrite the two components.

If a set of words is contained in a larger set and a second set is contained in a larger second set, then the empty word adjoined to the false-tagged copy of the smaller set and the true-tagged copy of the smaller second set is contained in the same construction on the two larger sets.

The empty word is preserved. A false-tagged word has its tail in the smaller set, hence in the larger set, and a true-tagged word has its tail in the smaller second set, hence in the larger second set.

If one set of tokens is contained in another, the token-level master of a construct on the smaller set is contained in the master on the larger set.

The proof is by induction on the construct. A constant is unchanged. The identity is the given inclusion. A sum or a product applies the tagged-union inclusion to the two inductive inclusions.

For a nonempty family of sets, if membership in the first operation on a union is membership in that operation on some member, and likewise for the second operation, then a word lies in the empty word adjoined to the false-tagged first operation and the true-tagged second operation on the union if and only if it lies in that construction for some member.

The empty word belongs to every such set, and the family is nonempty, so any member witnesses it. A false-tagged word has its tail in the first operation on the union, hence on some member, and that member witnesses the tagged word; the true tag is the same for the second operation. Conversely, a tagged word coming from some member has its tail in the corresponding operation on that member, hence on the union.

For a nonempty directed family of sets of tokens whose union is U, a word lies in the token-level master of a construct on U if and only if it lies in the master of that construct on some member of the family.

The proof is by induction on the construct, and the directedness hypothesis is not used. A constant value belongs to the image for every set, and the family is nonempty, so membership does not depend on which set is chosen. The identity is the given description of the union. A sum or a product is the tagged-union continuity lemma applied to the two inductive equivalences.

If every constant in a construct has the empty word in its master, and the empty word lies in a set of tokens, then the empty word lies in the token-level master of the construct on that set.

A constant uses the hypothesis on its master. The identity uses the hypothesis on the set. A sum or a product contains the empty word by the inserted root.

If every constant in a construct has the empty word in its master, then the empty word lies in every Kleene iterate of the token-level master, starting from the singleton of the empty word.

The zeroth iterate is that singleton. Each successor applies the previous lemma to the inductive hypothesis.

If every constant in a construct has the empty word in its master, each Kleene iterate is contained in the next.

The zeroth iterate is the singleton of the empty word, which the root lemma places in the first iterate. Each later step is monotonicity of the token-level master applied to the previous inclusion.

If every constant in a construct has the empty word in its master and one index is at most another, then the earlier Kleene iterate is contained in the later one.

The proof is by induction on the inequality. Equal indices give the same set. A successor step applies the one-step inclusion.

If every constant in a construct has the empty word in its master, the token-level master of the union of the Kleene iterates equals that union.

The range of the iterates is nonempty because it contains the zeroth iterate, and it is directed because the iterate at the maximum of two indices contains both. A word lies in the union exactly when it lies in some iterate. Continuity of the token-level master therefore equates membership in the master of the union with membership in the master of some iterate, which is the next iterate. In the other direction a word of the union lies in some iterate, and the one-step inclusion places that word in the master of the same iterate.

If every constant in a construct has the empty word in its master, some set of tokens contains the empty word and is fixed by the token-level master of the construct.

The union of the Kleene iterates contains the empty word because the zeroth iterate does, and the previous lemma says this union is a fixed point.

If every constant in a construct has the empty word in its master, some nonempty set of tokens has its one-neighbourhood system as a subsystem of the construct applied to that system.

The fixed-point lemma supplies a set containing the empty word and fixed by the token-level master, so the set is nonempty. Equality of that master with the neighbourhood-system master says the master of the construct on the one-neighbourhood system is that set, so the two systems have the same master. The only neighbourhood of the one-neighbourhood system equals this master, hence is a neighbourhood of the construct. The intersection of its two neighbourhoods is the set intersected with itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.ScottSys

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.map
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.tok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.singletonSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.mFun
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.RootedConst
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.mIter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.embBit_not_subset_cross

@[expose] public section

/-!
# Exercise 6.19 (Scott 1981, PRG-19, §6) — Part B: the functor algebra

> … Now generate all constructs `T(X)` formed by the constants (that is, `T(X) = 𝒟` for a fixed `𝒟`),
> by the identity (`T(X) = X`), and by sums and products (`T₀(X) + T₁(X)`, etc.). Show that these are
> all functors, continuous on maps, and monotone and continuous on domains.

This module formalizes **Part B**: the closed family of constructs `T(X)` over Scott's *uniform*
category of Exercise 6.19 — neighbourhood systems on `Δ ⊆ {0,1}*` with `∅ ∉ 𝒟` (the standing
hypothesis that makes the token-level sum `sumTok`/product `prodTok` of Part A genuine
*endo*-operations) and **strict** approximable maps.

## Contents

* `ScottSys` — an object of Scott's category: an `∅`-free neighbourhood system over `Str = {0,1}*`.
* The object actions `ScottSys.sum`/`ScottSys.prod` (Part A's `sumTok`/`prodTok`, repackaged so they
  stay inside the category) and the constant/identity objects.
* The **functorial action on maps**: `sumMapTok f₀ f₁ : (𝒟₀+𝒟₁) → (ℰ₀+ℰ₁)` and
  `prodMapTok f₀ f₁ : (𝒟₀×𝒟₁) → (ℰ₀×ℰ₁)`, each an approximable map, with strictness preservation
  (`sumMapTok` is *always* strict; `prodMapTok` is strict when both factors are).
* The **bifunctor laws**: both actions preserve identities and composition
  (`sumMapTok_id`/`sumMapTok_comp`, `prodMapTok_id`/`prodMapTok_comp`).
* The functor-expression algebra `FExpr` (constants, identity, sum, product), its object action
  `FExpr.obj`, its action on maps `FExpr.map`.

Scott asks to show these constructs are **all functors, continuous on maps, and monotone and
continuous on domains**; each is established here:

* **functors** — `FExpr.map_id` (`T(I)=I`) and `FExpr.map_comp` (`T(g∘f)=T(g)∘T(f)`), by induction;
  plus `FExpr.map_isStrict` (so `T` restricts to Scott's strict-map category).
* **continuous on maps** — `FExpr.map_mono` (a sharper map gives a sharper image) and
  `FExpr.map_continuous` (`λf. T(f)` preserves directed unions of maps); together these are exactly
  approximability of `λf. T(f)` (Exercise 2.13).
* **monotone on domains** — `FExpr.obj_subsystem` (`D ◁ E ⟹ T(D) ◁ T(E)`).
* **continuous on domains** — `FExpr.obj_continuous` (`λD. T(D)` preserves directed unions of
  subsystems, the form Scott uses in Theorem 6.14).

Because every construct stays over the single token type `{0,1}*`, the subdomain relation `◁` is
between systems on a common carrier, so the domain conditions need no carrier transport (unlike the
universe-polymorphic `Endofunctor DomainObj` form of Definitions 6.8/6.13).

This module also formalizes **Exercise 6.20**: writing `tok(𝒟) = 𝒟.master` for the underlying token
set and `{Γ}` for the one-neighbourhood system `singletonSys Γ`, the function `λΓ. tok(T({Γ}))` is
computed by the token-level recursion `mFun T` (`mFun_eq_master`), shown monotone (`mFun_mono`) and
continuous (`mFun_continuous`) on the domain `{Γ ∣ Λ ∈ Γ}`. Its least fixed point — the explicit
Kleene union `⋃ₙ mFunⁿ({Λ})` — gives a `Γ = tok(T({Γ}))` (`exists_tok_fixedPoint`), whence
`{Γ} ◁ T({Γ})` (`exists_singleton_subsystem`), exactly the hypothesis Theorem 6.14 needs.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-! ## Objects of Scott's category: `∅`-free systems over `{0,1}*` -/


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-! ## The functorial action of sum on maps -/


/-! ## The functorial action of product on maps -/


/-! ## The bifunctor laws: identities and composition are preserved -/

/-! ## The functor-expression algebra `T(X)` and the functor laws

*"Generate all constructs `T(X)` formed by the constants (`T(X) = 𝒟`), by the identity (`T(X) = X`),
and by sums and products."* -/


/-! ## Continuous on maps — the monotone half

Scott's *continuous on maps* (Definition 6.8) requires `λf. T(f)` to be approximable on the strict
function space; here we record its **monotonicity** (the order half of approximability — a sharper map
yields a sharper image), proved compositionally from the bifunctor combinators. -/

/-! ## Monotone on domains

Scott's *monotone on domains* (Definition 6.13): a subdomain relation `D ◁ E` is carried to
`T(D) ◁ T(E)`. Because every construct here stays over the single token type `{0,1}*`, the relation is
between systems on a common carrier (no transport needed), and the bifunctor combinators carry `◁`
componentwise. -/

/-! ## Continuous on domains

Scott's *continuous on domains* (Definition 6.13): `λD. T(D)` preserves directed unions of
subsystems. Concretely, if `U` is the union of a non-empty `◁`-directed family `ℱ` of subsystems of
`U`, then every neighbourhood of `T(U)` already appears in some `T(D)` with `D ∈ ℱ` (and conversely).
The forward direction is by induction; the products use directedness to merge the two component
witnesses into a single `D`. -/

/-! ## Continuous on maps — full directed-sup preservation

Scott's *continuous on maps* (Definition 6.8): `λf. T(f)` is approximable, equivalently (Exercise
2.13) it is continuous — monotone (`map_mono`) and preserving directed unions of maps. If `f` is the
pointwise union of a non-empty directed family `gᵢ`, then `T(f)` is the pointwise union of the
`T(gᵢ)`. The products use directedness to merge the two component witnesses. -/

/-! ## Exercise 6.20 — `λΓ. tok(T({Γ}))` is continuous, hence a fixed point exists

> For any system `𝒟` let `tok(𝒟)` be the underlying set of tokens, so that `𝒟` is a system over
> `tok(𝒟)`. For the category of Exercise 6.19 show that the function `λΓ. tok(T({Γ}))` is continuous
> on the domain `{Γ ⊆ {0,1}* ∣ Λ ∈ Γ}`, where `T` is any of the functors generated in 6.19. Conclude
> that there must exist a set `Γ = tok(T({Γ}))`, so that `{Γ} ◁ T({Γ})`, and so 6.14 applies.

Here `tok(𝒟) = 𝒟.master` (the master neighbourhood *is* the token set `Δ`, since `𝒟 ⊆ 𝒫(Δ)`), and
`{Γ}` is the one-neighbourhood system `singletonSys Γ` with master `Γ`. The key simplification is
that the *master* of `T({Γ})` is computed by a tiny token-level recursion `mFun T` that needs no
`NeighborhoodSystem` data at all: constants are constant, the identity returns `Γ`, and **both** sum
and product return `{Λ} ∪ 0·(…) ∪ 1·(…)` (`sumTokMaster = prodTokNbhd` on masters). `mFun_eq_master`
identifies `mFun T Γ` with `tok(T({Γ}))`. The function `mFun T` is monotone (`mFun_mono`) and
continuous — in fact fully additive — on the powerset of `{0,1}*` (`mFun_continuous`), so its
restriction to `{Γ ∣ Λ ∈ Γ}` is continuous on that domain. The least fixed point above the bottom
`{Λ}` is the explicit Kleene union `⋃ₙ mFunⁿ({Λ})` (`mIter`), giving `Γ = tok(T({Γ}))`
(`exists_tok_fixedPoint`) and hence `{Γ} ◁ T({Γ})` (`exists_singleton_subsystem`), exactly the
hypothesis Theorem 6.14 needs. (For the bottom to stay in the domain we need `Λ ∈ tok(C)` for the
constant systems `C`; this is recorded by `FExpr.RootedConst`, and holds automatically for sums and
products since their masters contain `Λ`.) -/


/-- `mFun T Γ` is exactly the token set `tok(T({Γ})) = (T.obj {Γ}).sys.master`. -/
theorem mFun_eq_master : (T : FExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    mFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]
  | .prod T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]

/-! ### Monotone on the domain -/

/-- Monotonicity of the tagged-union shape shared by sum and product. -/
theorem insertTag_mono {p q p' q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') :
    insert ([] : Str) (embBit false p ∪ embBit true q)
      ⊆ insert ([] : Str) (embBit false p' ∪ embBit true q') := by
  rintro w (rfl | hw | hw)
  · exact Or.inl rfl
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inl ⟨w', rfl, hp hw'⟩)
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inr ⟨w', rfl, hq hw'⟩)

/-- **`λΓ. tok(T({Γ}))` is monotone on the domain.** -/
theorem mFun_mono (T : FExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : mFun T Γ ⊆ mFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

/-! ### Continuous on the domain -/

/-- Continuity (full additivity) of the tagged-union shape shared by sum and product. -/
theorem insertTag_continuous {ℱ : Set (Set Str)} {U : Set Str} (hne : ℱ.Nonempty)
    {p q : Set Str → Set Str}
    (hp : ∀ w, w ∈ p U ↔ ∃ Γ ∈ ℱ, w ∈ p Γ)
    (hq : ∀ w, w ∈ q U ↔ ∃ Γ ∈ ℱ, w ∈ q Γ) (w : Str) :
    (w ∈ insert ([] : Str) (embBit false (p U) ∪ embBit true (q U)))
      ↔ ∃ Γ ∈ ℱ, w ∈ insert ([] : Str) (embBit false (p Γ) ∪ embBit true (q Γ)) := by
  simp only [Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro (rfl | hw | hw)
    · obtain ⟨Γ, hΓ⟩ := hne; exact ⟨Γ, hΓ, Or.inl rfl⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hpΓ⟩ := (hp w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inl ⟨w', rfl, hpΓ⟩)⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hqΓ⟩ := (hq w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inr ⟨w', rfl, hqΓ⟩)⟩
  · rintro ⟨Γ, hΓ, (rfl | hw | hw)⟩
    · exact Or.inl rfl
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inl ⟨w', rfl, (hp w').mpr ⟨Γ, hΓ, hw'⟩⟩)
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inr ⟨w', rfl, (hq w').mpr ⟨Γ, hΓ, hw'⟩⟩)

/-- **`λΓ. tok(T({Γ}))` is continuous on the domain `{Γ ∣ Λ ∈ Γ}`.** For a non-empty `⊆`-directed
family `ℱ` with union `U`, the token set of `T({U})` is the union of those of the `T({Γ})`. (The
proof in fact establishes full additivity — directedness is not needed for the master level — but the
statement is the directed-sup form Scott calls *continuous*.) -/
theorem mFun_continuous (T : FExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ mFun T U ↔ ∃ Γ ∈ ℱ, w ∈ mFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w

/-! ### A fixed point `Γ = tok(T({Γ}))` — so `{Γ} ◁ T({Γ})` and 6.14 applies -/


/-- If `Λ ∈ Γ` then `Λ ∈ tok(T({Γ}))` — so `λΓ. tok(T({Γ}))` is an endofunction of the domain. -/
theorem mFun_nil_mem : ∀ (T : FExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ mFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _


theorem nil_mem_mIter (T : FExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ mIter T n
  | 0 => rfl
  | n + 1 => mFun_nil_mem T hT (nil_mem_mIter T hT n)

theorem mIter_mono_step (T : FExpr) (hT : T.RootedConst) :
    ∀ n, mIter T n ⊆ mIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact mFun_nil_mem T hT rfl
  | n + 1 => mFun_mono T (mIter_mono_step T hT n)

theorem mIter_mono (T : FExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    mIter T m ⊆ mIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact mIter_mono_step T hT _ (ih hx)

/-- The Kleene union is a **fixed point** of `λΓ. tok(T({Γ}))`. -/
theorem mFun_iter_fixed (T : FExpr) (hT : T.RootedConst) :
    mFun T (⋃ n, mIter T n) = ⋃ n, mIter T n := by
  have hstep := mIter_mono_step T hT
  have hne : (Set.range (mIter T)).Nonempty := ⟨mIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (mIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨mIter T (max i j), ⟨max i j, rfl⟩,
      mIter_mono T hT (le_max_left i j), mIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, mIter T n) ↔ ∃ S ∈ Set.range (mIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨mIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [mFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨mIter T n, ⟨n, rfl⟩, hstep n hn⟩

/-- **The conclusion of Exercise 6.20 (token level).** For any construct `T` whose constants contain
`Λ`, there is a set `Γ` with `Λ ∈ Γ` and `Γ = tok(T({Γ}))`. -/
theorem exists_tok_fixedPoint (T : FExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ mFun T Γ = Γ :=
  ⟨⋃ n, mIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_mIter T hT 0⟩, mFun_iter_fixed T hT⟩

/-- **The conclusion of Exercise 6.20 (object level): `{Γ} ◁ T({Γ})`, so Theorem 6.14 applies.**
From the fixed point `Γ = tok(T({Γ}))`, the one-neighbourhood system `{Γ}` is a subsystem of
`T({Γ})`: they share the master `Γ`, and `Γ` is a (the master) neighbourhood of `T({Γ})`. -/
theorem exists_singleton_subsystem (T : FExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := exists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩
  -- `tok(T({Γ})) = Γ` (note `tok` is definitionally `.sys.master`).
  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (mFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  · -- master_eq: `Γ = tok(T({Γ}))`
    exact hmaster.symm
  · -- sub: the only neighbourhood `Γ` of `{Γ}` is the master of `T({Γ})`
    intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  · -- inter_closed: trivial, both neighbourhoods are `Γ`
    intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]
end Exercise619
end DomainTheory.NeighbourhoodSystems
