import QStab.QHL.Target.CEval

/-! # QClifford Hoare triples (Floyd-Hoare model-theoretic layer style)

The model-theoretic Hoare triple at the QClifford gate level, mirroring
`QHL.Source.hoare_triple` for the QStab side.

  `⦃P⦄ c ⦃Q⦄_c` means: for every initial error state `es` satisfying
  `P`, every (in fact, the unique) `es'` reachable by executing `c`
  from `es` satisfies `Q`.

We use double white brackets `⦃ ⦄` to typographically distinguish
QClifford triples from QStab triples `{{ }}` in mixed contexts (e.g.,
in the proof compiler where both appear).
-/

namespace QHL.Target

open QStab.QClifford

/-- Assertions over QClifford error states. -/
abbrev AssertionC (nq : Nat) := ErrorState nq → Prop

/-- A Hoare triple at the QClifford level. -/
def hoare_triple_c {nq : Nat}
    (Pre : AssertionC nq) (c : Circuit nq) (Post : AssertionC nq) : Prop :=
  ∀ (es es' : ErrorState nq), cevalC c es es' → Pre es → Post es'

/-- QClifford Hoare-triple notation. White brackets `⦃ ⦄` distinguish
    from QStab's `{{ }}`. -/
notation:90 "⦃" Pre "⦄ " c " ⦃" Post "⦄c" => hoare_triple_c Pre c Post

/-- Pointwise implication on assertions (the consequence-rule premise). -/
def AssertionC.implies {nq : Nat} (P Q : AssertionC nq) : Prop :=
  ∀ es, P es → Q es

end QHL.Target
