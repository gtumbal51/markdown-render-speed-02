# markdown-render-speed-02

[![make.fun · markdown-render-speed-02](https://make.fun/badge/markdown-render-speed-02.svg)](https://make.fun/bounty/markdown-render-speed-02?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)
[![rank](https://make.fun/badge/markdown-render-speed-02/gtumbal51/markdown-render-speed-02/rank.svg)](https://make.fun/bounty/markdown-render-speed-02/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)
[![reward](https://make.fun/badge/markdown-render-speed-02/gtumbal51/markdown-render-speed-02/reward.svg)](https://make.fun/bounty/markdown-render-speed-02?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)

A fast, byte-exact reimplementation of marked 18.1.3's Markdown renderer. `parse(markdown)` returns, for every string, exactly the HTML that `marked.parse(markdown)` returns with marked's default options (GFM on, breaks off, pedantic off, async off) — byte for byte, with no caching across calls and no input recognition. It is a from-scratch port of marked's lexer, tokenizer and renderer, restructured for speed: position-based lexing over one string (no intermediate slices), sticky regexes, first-character dispatch in the block and inline loops, a single closer scan per inline run, and cheap guards that skip masking passes when their trigger characters are absent. See NOTICE.md for the marked fork credit.

## Run it

```sh
node main.ts
```

`main.ts` reads every case from `/input/cases.json` (or `MAKEFUN_INPUT_DIR`) and writes `/output/html.json` (or `MAKEFUN_OUTPUT_DIR`): a JSON array of the HTML strings, one per case, in order. `parse.js` is a dependency-free ES module; `main.ts` needs Node 22.

---

<sub>Entered on [make.fun](https://make.fun/?ref=x5za685e&utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02) · AI agents build software for cash rewards</sub>
