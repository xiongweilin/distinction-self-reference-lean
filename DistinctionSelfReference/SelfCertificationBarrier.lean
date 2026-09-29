import DistinctionSelfReference.VerifierMigration

namespace DistinctionSelfReference
namespace SelfCertificationBarrier

universe u

/--
A minimal abstract interface for a provability predicate satisfying Löb's rule.
This isolates exactly the meta-logical ingredient needed by the RSI layer,
without rebuilding arithmetic syntax or diagonalization locally.
-/
structure LobInterface (Sentence : Type u) where
  Provable : Sentence → Prop
  box : Sentence → Sentence
  imp : Sentence → Sentence → Sentence
  lob :
    ∀ phi,
      Provable (imp (box phi) phi) →
      Provable phi

namespace LobInterface

variable {Sentence : Type u}

def InternalReflection
    (L : LobInterface Sentence)
    (phi : Sentence) : Prop :=
  L.Provable (L.imp (L.box phi) phi)

/--
Löb barrier: proving one's own reflection principle for a sentence collapses
to proving that sentence itself.
-/
theorem reflection_collapses_to_proof
    (L : LobInterface Sentence)
    (phi : Sentence)
    (hreflect : L.InternalReflection phi) :
    L.Provable phi :=
  L.lob phi hreflect

/--
Contrapositive form useful for verifier migration: any sentence not already
provable cannot have its internal reflection principle proved either.
-/
theorem unprovable_blocks_internal_reflection
    (L : LobInterface Sentence)
    (phi : Sentence)
    (hunprovable : ¬ L.Provable phi) :
    ¬ L.InternalReflection phi := by
  intro hreflect
  exact hunprovable (L.reflection_collapses_to_proof phi hreflect)

end LobInterface

/--
A concrete verifier family enters the Löb regime once semantic soundness claims
are represented by sentences of the same internal provability system.
-/
structure SoundnessEncoding
    (Verifier : Type u)
    (Sentence : Type u) where
  soundSentence : Verifier → Sentence

def LobSelfCertification
    {Verifier Sentence : Type u}
    (L : LobInterface Sentence)
    (E : SoundnessEncoding Verifier Sentence)
    (v : Verifier) : Prop :=
  L.InternalReflection (E.soundSentence v)

/--
Exact interface boundary: if self-certification means proving internal
reflection for the verifier's own soundness sentence, Löb turns that
certificate into an internal proof of the soundness sentence itself.
-/
theorem lob_barrier_for_verifier_selfCertification
    {Verifier Sentence : Type u}
    (L : LobInterface Sentence)
    (E : SoundnessEncoding Verifier Sentence)
    (v : Verifier)
    (hcert : LobSelfCertification L E v) :
    L.Provable (E.soundSentence v) :=
  L.reflection_collapses_to_proof (E.soundSentence v) hcert

/--
Therefore any verifier soundness sentence known to be unprovable internally
cannot receive this form of self-certification.
-/
theorem unprovable_soundness_blocks_lob_selfCertification
    {Verifier Sentence : Type u}
    (L : LobInterface Sentence)
    (E : SoundnessEncoding Verifier Sentence)
    (v : Verifier)
    (hunprovable : ¬ L.Provable (E.soundSentence v)) :
    ¬ LobSelfCertification L E v := by
  intro hcert
  exact hunprovable
    (lob_barrier_for_verifier_selfCertification L E v hcert)

/--
A generic certification graph between verifier versions. Sound is semantic;
Certifies is merely an internal acceptance/certification relation.
-/
structure CertificationSystem (Verifier : Type u) where
  Certifies : Verifier → Verifier → Prop
  Sound : Verifier → Prop

namespace CertificationSystem

variable {Verifier : Type u}

def SelfCertified
    (C : CertificationSystem Verifier)
    (v : Verifier) : Prop :=
  C.Certifies v v

/--
A genuinely semantic migration law: certification transfers soundness only
from an already-sound predecessor.
-/
def SoundnessTransfer
    (C : CertificationSystem Verifier) : Prop :=
  ∀ old new,
    C.Sound old →
    C.Certifies old new →
    C.Sound new

def Chain
    (C : CertificationSystem Verifier)
    (versions : Nat → Verifier) : Prop :=
  ∀ n, C.Certifies (versions n) (versions (n + 1))

/--
With a non-circular anchor, predecessor certification propagates soundness.
-/
theorem sound_along_chain
    (C : CertificationSystem Verifier)
    (versions : Nat → Verifier)
    (htransfer : C.SoundnessTransfer)
    (hchain : C.Chain versions)
    (h0 : C.Sound (versions 0)) :
    ∀ n, C.Sound (versions n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact htransfer (versions n) (versions (n + 1)) ih (hchain n)

end CertificationSystem

namespace CircularCounterexample

/--
Every verifier certifies every verifier, including itself, while semantic
soundness is false for one version. This is the finite witness that internal
certification alone carries no semantic guarantee.
-/
def system : CertificationSystem Bool where
  Certifies := fun _ _ => True
  Sound := fun v => v = false

theorem every_version_selfCertified (v : Bool) :
    system.SelfCertified v := by
  trivial

theorem true_version_unsound :
    ¬ system.Sound true := by
  simp [system]

theorem selfCertification_not_sufficient :
    ¬ ∀ v, system.SelfCertified v → system.Sound v := by
  intro h
  exact true_version_unsound (h true (every_version_selfCertified true))

/--
Even an infinite certification chain can be internally valid everywhere while
starting from — and remaining at — an unsound verifier.
-/
def badChain (_ : Nat) : Bool := true

theorem badChain_certified :
    system.Chain badChain := by
  intro n
  trivial

theorem badChain_unsound_everywhere :
    ∀ n, ¬ system.Sound (badChain n) := by
  intro n
  simp [badChain, system]

end CircularCounterexample

namespace GroundedEscape

/--
An external grounding predicate is deliberately not defined in terms of the
system's own certification relation.
-/
structure GroundedSystem (Verifier : Type u)
    extends CertificationSystem Verifier where
  Grounded : Verifier → Prop
  grounding_sound :
    ∀ v, Grounded v → Sound v

namespace GroundedSystem

variable {Verifier : Type u}

theorem sound_from_ground
    (G : GroundedSystem Verifier)
    (v : Verifier)
    (hground : G.Grounded v) :
    G.Sound v :=
  G.grounding_sound v hground

/--
One externally grounded root plus a sound transfer law is enough for a whole
self-modifying certification chain.
-/
theorem sound_chain_from_grounded_root
    (G : GroundedSystem Verifier)
    (versions : Nat → Verifier)
    (htransfer : G.toCertificationSystem.SoundnessTransfer)
    (hchain : G.toCertificationSystem.Chain versions)
    (hground : G.Grounded (versions 0)) :
    ∀ n, G.Sound (versions n) := by
  apply G.toCertificationSystem.sound_along_chain versions htransfer hchain
  exact G.grounding_sound (versions 0) hground

end GroundedSystem
end GroundedEscape

end SelfCertificationBarrier
end DistinctionSelfReference
