import Text.Lex.Core
import Text.Lex.Tokenizer
import Text.Lex.Util

-- This module re-exports the public interfaces of the lexer library,
-- providing a single point of entry for users.

namespace Text.Lex

  -- Re-export the core types and functions
  export Text.Lex.Core (Recognise Lexer)

  -- Re-export the tokenizer data type and its associated functions
  export Text.Lex.Tokenizer (Tokenizer)

  -- Re-export the utility functions and combinators
  export Text.Lex.Util

end Text.Lex
