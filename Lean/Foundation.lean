import Foundation.Category
import Foundation.DG
import Foundation.Completion
import Foundation.Rewriting

/-!
# Foundation

This root namespace collects the reusable categorical, dg, completion, and rewriting
infrastructure extracted from the legacy development. Files under `Foundation` are meant to
stand on their own as honest mathematics and should never depend on project-specific `TraceCalc`
modules.
-/

namespace Foundation

/-- `Foundation` is a re-export hub for the extracted core layers. -/
abbrev ChapterLoaded : Type := PUnit

/-- Canonical witness that this chapter namespace is loaded. -/
def chapterLoaded : ChapterLoaded := PUnit.unit

end Foundation
