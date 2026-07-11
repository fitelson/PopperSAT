# PopperSAT

Current release: **1.0**

PopperSAT is a browser-based decision procedure for satisfiability of constraints on Popper probability functions. Conditional probability is primitive, so probabilities must be written in two-place form, such as `Pr(A | true)`.

## Installation

### Requirements

- (Optional) [Visual Studio Code (VSCode)](https://code.visualstudio.com)
  - Any plain-text editor and terminal will do.
- [Node + NVM](https://nodejs.org/en/download)

### Steps
1. Open your terminal of choice (could be in VSCode).
2. Navigate to desired directory.
3. Run `git clone https://github.com/fitelson/PopperSAT.git`.
4. Run `cd PopperSAT`.
5. Run `npm install`.

## Running the development server

```bash
npm run dev
```

A local PopperSAT URL will appear in your terminal.

## Verification

```bash
npm run build
npm test
```

## Contributors

- Branden Fitelson
- OpenAI Codex
