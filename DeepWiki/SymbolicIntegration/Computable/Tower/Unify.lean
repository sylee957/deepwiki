import DeepWiki.SymbolicIntegration.Computable.Tower.Integrate
import DeepWiki.SymbolicIntegration.Computable.CanonicalFieldIdentity

/-! # Tower canonical-representation re-export waypoint

Bundles `Tower.Integrate` (the tower integration engine and the fuel-free
`canonicalRepresentationFastGWf`) with `CanonicalFieldIdentity` (the field-identity bridge). The fuel'd
`canonicalRepresentationFastG` reconstruction/proper probes that formerly lived here were retired together
with the fuel'd §5 Tower API; downstream catalog chapters import this module for the bundled dependency. -/
