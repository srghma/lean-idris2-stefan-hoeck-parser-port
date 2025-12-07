import Text.Parse.Core
import Text.Parse.Manual
import Text.Parse.Syntax
import Text.Lex.Manual -- For Bounded, InnerError

-- This module re-exports the public interfaces of the parser library,
-- providing a single point of entry for users.

namespace Text.Parse

  -- Re-export the core types and functions
  export Text.Parse.Core (Grammar Res parse)

  -- Re-export the manual parsing utilities
  export Text.Parse.Manual (terminal exact peek)

  -- Re-export the high-level syntax
  export Text.Parse.Syntax (pure ap seqRight seqLeft between optional many)

  -- Re-export fundamental types from the lexer that are used in parsing
  export Text.Lex.Manual (Bounded InnerError)

end Text.Parse
