import Mathlib

open IsDedekindDomain HeightOneSpectrum

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
variable (v : HeightOneSpectrum A)

instance : letI : UniformSpace K := v.adicValued.toUniformSpace
  NormedField K :=

instance : NormedField (adicCompletion K v) := sorry
