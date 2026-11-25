import Certified
import SerialOutput
import OrbitHardness
import TraceReadout
import TraceSelect
import Chronology
import Majority

set_option format.width 120
set_option pp.funBinderTypes true
set_option pp.fullNames true
set_option pp.maxSteps 100000
set_option pp.deepTerms true

#check TwoScans.Certified.universality
#print axioms TwoScans.Certified.universality

#check TwoScans.Prize.serial_universal_strings
#print axioms TwoScans.Prize.serial_universal_strings

#check TwoScans.OrbitHardness.complete_indexed
#print axioms TwoScans.OrbitHardness.complete_indexed

#check TwoScans.TraceReadout.regular_detection
#print axioms TwoScans.TraceReadout.regular_detection

#check TwoScans.TraceSelect.readAt_sound
#print axioms TwoScans.TraceSelect.readAt_sound

#check TwoScans.TraceSelect.readAt_cofinal
#print axioms TwoScans.TraceSelect.readAt_cofinal

#check TwoScans.Chronology.trajectory
#print axioms TwoScans.Chronology.trajectory

#check TwoScans.Chronology.linear_seed
#print axioms TwoScans.Chronology.linear_seed

#check TwoScans.Majority.universal_strings
#print axioms TwoScans.Majority.universal_strings
