//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.

#include<string>
#include<iostream>
using namespace std;

enum Token
{
    TOK_EOF = -1,

    // commands
    TOK_FUN = -2,
    TOK_IMPORT = -3,
    TOK_VAR= -4,
    

    // primary
    TOK_IDENT = -6,
    TOK_INT = -7,
    TOK_FLOAT = -8,
};

static std::string identifierStr; // Filled in if TOK_IDENT
static int intVal;                // Filled in if TOK_INT
static double floatVal;           // Filled in if TOK_FLOAT

/// gettok - Return the next token from standard input.
static int gettok()
{
    static int lastChar = ' ';

    // Skip any whitespace.
    while (isspace(lastChar))
        lastChar = getchar();

    // identifier: [a-zA-Z][a-zA-Z0-9]*
    if (isalpha(lastChar))
    {
        identifierStr = lastChar;

        while (isalnum((lastChar = getchar())))
            identifierStr += lastChar;

        if (identifierStr == "fun")
            return TOK_FUN;

        if (identifierStr == "import")
            return TOK_IMPORT;

        if (identifierStr == "var")
            return TOK_VAR;
        

        return TOK_IDENT;
    }

    // Integer: [0-9]+ or Float: [0-9]+.[0-9]+
    if (isdigit(lastChar) || (lastChar == '.'))
    {
        std::string numStr;
        bool isFloat = false;

        do
        {
            numStr += lastChar;

            if (lastChar == '.')
            {
                if (isFloat)
                {
                    break;
                }

                isFloat = true;
            }

            lastChar = getchar();
        } while (isdigit(lastChar) || (!isFloat && lastChar == '.'));

        if (isFloat)
        {
            floatVal = strtod(numStr.c_str(), nullptr);
            return TOK_FLOAT;
        }
        else
        {
            intVal = strtol(numStr.c_str(), nullptr, 10);
            return TOK_INT;
        }
    }

    if (lastChar == '/' && ((lastChar = getchar()) == '/'))
    {
        // Comment until end of line.
        // single-line comment
        do
            lastChar = getchar();
        while (lastChar != EOF && lastChar != '\n' && lastChar != '\r');

        if (lastChar != EOF)
            return gettok();
    }
    else if (lastChar == '/' && ((lastChar = getchar()) == '*'))
    {
        // Comment until the closing '*/'.
        // multi-line comment
        do
            lastChar = getchar();
        while (lastChar != EOF && lastChar != '*' && lastChar != '/');

        if (lastChar != EOF)
            return gettok();
    }

    // Check for end of file. Don't eat the EOF.
    if (lastChar == EOF)
        return TOK_EOF;

    // Otherwise, just return the character as its ascii value.
    int thisChar = lastChar;
    lastChar = getchar();
    return thisChar;
}

  int main(){
    while (true){
      int tok = gettok();
      cout << "got token: " << tok << endl;
    }
}