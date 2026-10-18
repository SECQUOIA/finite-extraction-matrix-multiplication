import formalization.RationalAlgorithmTransportBridge

-- The two endpoint theorems of Section 11.3 of the paper.
#check @MatrixDimensionAudit.RationalAlgorithmTransportBridge.omega_le_nine_fourths
#check @MatrixDimensionAudit.RationalAlgorithmTransportBridge.algorithms_with_exponent_slack

-- Both should report only [propext, Classical.choice, Quot.sound].
#print axioms MatrixDimensionAudit.RationalAlgorithmTransportBridge.omega_le_nine_fourths
#print axioms MatrixDimensionAudit.RationalAlgorithmTransportBridge.algorithms_with_exponent_slack
