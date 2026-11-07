# Recreio

Jogo de tabuleiro 7x7 no estilo mesa de futebol de botão: 6 alunos e 1 goleiro de cada lado,
movimentos por cartas. Vence quem capturar o goleiro adversário ou chegar no gol dele (a casa
onde o goleiro começou).

- `LAWS.bend`: as regras que nunca podem quebrar (escritas por humano).
- `PROOF.bend`: as provas das leis (as que faltam aparecem como TODO).
- `game.bend`: a lógica inteira do jogo, incluindo o baralho, o bot e as chances.
- `engine/`: a engine compilada para JS (`game.mjs` + tipos `game.d.mts`), usada pelos testes.
- `app/`: o jogo (Vite + React + React Three Fiber + Effect). `app/src/engine/game.ts` é gerado.
- `relay/`: Worker da Cloudflare que só repassa mensagens entre dois jogadores.
- `tools/dts/`: gerador dos tipos TypeScript da engine, escrito em Bend, com as próprias leis provadas.
  Tipos com `# ts: union` em cima viram uniões discriminadas (`switch (x.$)`); os outros ficam opacos.

## Depois de mudar a engine

```sh
bend game.bend -o engine/game.mjs                                    # compila a engine
bend tools/dts/main.bend -o tools/dts/bend-dts                       # compila o gerador (uma vez)
tools/dts/bend-dts game.bend engine/game.d.mts                       # tipos ao lado do .mjs
tools/dts/bend-dts game.bend app/src/engine/game.ts engine/game.mjs  # módulo TS do app
```

## Rodar

```sh
cd app && npm install && npm run dev             # http://127.0.0.1:5173
cd relay && npx wrangler@4 dev --port 8799       # relay local, para o modo "com um amigo"
cd app && npm run build                          # site estático em app/dist
```

## Publicar (Cloudflare)

O jogo está em https://recreio.sugiyamalabs.com (Workers com arquivos estáticos, `app/wrangler.jsonc`)
e o relay em wss://recreio-relay.williansugiyama.workers.dev (`relay/wrangler.toml`).

```sh
cd relay && npx wrangler@4 deploy                # relay
cd app && npm run deploy                         # build + publica o jogo
```

## Testar

```sh
bend PROOF.bend                  # provas do jogo (SOME PROOFS FAIL enquanto houver lei aberta)
bend tools/dts/PROOF.bend        # provas do gerador de tipos (todas fechadas)
node test/laws.mjs 2000          # 2000 partidas aleatórias checando as leis jogada a jogada
node test/online.mjs             # dois jogadores pelo relay local, com sorteio e provas de carta
node test/relay.mjs              # o relay local: sala de 2, mensagem só para o outro e igual, aviso de saída
cd app && npm run test:table     # no Brave: a mesa 3D mostra sempre o tabuleiro do motor (precisa do npm run dev)
npx -y -p typescript@5 tsc --noEmit --strict --module nodenext --moduleResolution nodenext --target es2022 test/types-check.ts
npx -y -p typescript@5 tsc --noEmit --strict --module nodenext --moduleResolution nodenext --target es2022 --allowImportingTsExtensions test/types-check-module.ts
```
