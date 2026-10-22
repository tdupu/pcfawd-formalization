# Tau Ceti normalization-finiteness sources

These nine Lean modules are copied from the local Tau Ceti checkout at
`85ed0984159b8de1ed8c11541105bb1d89c787e4` (Apache 2.0; source headers
retain the Tau Ceti copyright and authorship). Only the local import paths
were changed from `TauCeti.*` to `Pcf.Vendor.TauCeti.*`; declaration names
and proofs were preserved.

The source checkout used Lean `4.35.0` and Mathlib revision
`074063781836922cb02701cd12943c9f51731afa`. All nine modules also
compile in this repository with Lean `4.35.0` and its pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The endpoint `TauCeti.IsIntegralClosure.finite_mvPolynomial` proves finiteness
of the integral closure of a polynomial ring over any field in a finite
fraction-field extension, with no separability assumption. The PCF project
uses it in `Pcf.Bounding.GlobalNormalizationFinite` to remove the previous
characteristic-zero restriction from finite-type normalization.
