import Liu.CoverControl

-- Expected failure. Requiring a remaining box at the origin would be necessary for coverage.
example : Liu.Certificate.withoutCentral.any Liu.Certificate.atOrigin = true := by
  rw [Liu.Certificate.withoutCentral_any_false]
  decide
