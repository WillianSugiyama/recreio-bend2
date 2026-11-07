import Base
import ./game.bend as G

# Como ler uma lei:
#   for x: T          ->  "para todo x"
#   for nome: {...}   ->  "SE isso for verdade"
#   ultima linha      ->  "ENTAO isso tem que ser verdade"
# G.after(setup, moves) e o jogo depois de qualquer comeco (par ou impar + sorteio)
# e qualquer sequencia de jogadas, entao toda lei vale para qualquer partida possivel.

# ============ QUEM COMEÇA ============
# Cada jogador escolhe uma moeda secreta no próprio aparelho; quem começa sai das duas juntas.

# O azul não escolhe quem começa: qualquer que seja a moeda dele, a do vermelho ainda pode
# fazer qualquer lado começar.
law blue_cannot_choose_who_starts:
  for blue: G.Secret
  for side: G.Side
  exs red: G.Secret
  {G.Setup.starter(G.Setup{blue, red}) == side : G.Side}

# O vermelho também não.
law red_cannot_choose_who_starts:
  for red: G.Secret
  for side: G.Side
  exs blue: G.Secret
  {G.Setup.starter(G.Setup{blue, red}) == side : G.Side}

# Quem o sorteio escolheu faz a primeira jogada.
law starter_moves_first:
  for +setup: G.Setup
  {G.turn_of(G.after(setup, Nil{})) == G.Setup.starter(setup) : G.Side}

# ============ SORTEIO SEM TRAPACA ============
# Nao existe "dealer": cada jogador escolhe um segredo no proprio aparelho e o sorteio
# sai dos dois juntos. A criptografia (hash e cifra) e assumida segura: as leis provam
# o protocolo em volta dela, nao a matematica dela.

# O azul nao controla o sorteio: qualquer que seja o segredo dele, o segredo do
# vermelho ainda pode levar a qualquer distribuicao valida.
law blue_cannot_force_the_deal:
  for blue: G.Secret
  for +deal: G.Deal
  for valid: {G.Deal.is_valid(deal) == True{} : Bool}
  exs red: G.Secret
  {G.deal_from(blue, red) == deal : G.Deal}

# O vermelho tambem nao.
law red_cannot_force_the_deal:
  for red: G.Secret
  for +deal: G.Deal
  for valid: {G.Deal.is_valid(deal) == True{} : Bool}
  exs blue: G.Secret
  {G.deal_from(blue, red) == deal : G.Deal}

# Todo sorteio e valido: 5 cartas diferentes, todas do baralho.
law every_deal_is_valid:
  for blue: G.Secret
  for red: G.Secret
  {G.Deal.is_valid(G.deal_from(blue, red)) == True{} : Bool}

# As cartas iniciais de cada jogador sao as do sorteio.
law starting_hands_come_from_deal:
  for +setup: G.Setup
  for +side: G.Side
  {G.own_cards(G.after(setup, Nil{}), side) == G.Deal.hand_of(G.Setup.deal(setup), side) : List<&2, U32>}

# Jogar uma carta exige provar que ela esta na sua mao; sem prova, a jogada e recusada.
# (Assim nem um app modificado consegue jogar carta que nao tem.)
law unproven_card_is_rejected:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +move: G.Action
  for unproven: {G.card_proven(G.after(setup, moves), move) == False{} : Bool}
  {G.is_legal(G.after(setup, moves), move) == False{} : Bool}

# ============ BARALHO ============

# O baralho tem 18 cartas.
law deck_has_18_cards:
  {G.deck_size() == 18n : Nat}

# Nenhuma carta anda mais de 3 casas.
law cards_reach_at_most_3:
  {Nat.is_le(G.deck_max_step(), 3n) == True{} : Bool}

# Todo movimento tem o espelho: se vai pra direita, tambem vai pra esquerda.
# Vale para horizontal, diagonal pra cima, diagonal pra baixo e os de "cavalo".
law cards_mirror_left_right:
  for +i: Nat
  for in_deck: {Nat.is_lt(i, 18n) == True{} : Bool}
  for +step: G.Step
  for has: {G.card_has(G.deck_card(i), step) == True{} : Bool}
  {G.card_has(G.deck_card(i), G.Step.mirror(step)) == True{} : Bool}

# Movimento vertical vem em par: se vai pra cima, tambem vai pra baixo.
law vertical_goes_both_ways:
  for +i: Nat
  for in_deck: {Nat.is_lt(i, 18n) == True{} : Bool}
  for +step: G.Step
  for has: {G.card_has(G.deck_card(i), step) == True{} : Bool}
  for vertical: {G.Step.is_vertical(step) == True{} : Bool}
  {G.card_has(G.deck_card(i), G.Step.flip(step)) == True{} : Bool}

# Nenhuma carta prende as pecas: com qualquer carta, um grupo de ate 7 pecas do mesmo time
# sempre tem alguma peca com para onde ir. E isso que garante a lei never_stuck la embaixo.
law cards_never_trap:
  {G.deck_never_traps() == True{} : Bool}

# Sempre existem 5 cartas em jogo: 2 de cada jogador + 1 na mesa.
law always_five_cards:
  for setup: G.Setup
  for moves: List<&2, G.Action>
  {G.card_count(G.after(setup, moves)) == 5n : Nat}

# ============ JOGADAS ============

# Enquanto o jogo nao acabou, quem joga sempre tem uma jogada valida.
# Sem regra reserva: o baralho tem que ser desenhado para isso nunca falhar.
law never_stuck:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for not_over: {G.is_over(G.after(setup, moves)) == False{} : Bool}
  {G.has_legal_move(G.after(setup, moves)) == True{} : Bool}

# Depois de uma jogada valida, a vez passa para o outro.
law turn_alternates:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +move: G.Action
  for legal: {G.is_legal(G.after(setup, moves), move) == True{} : Bool}
  +before = G.after(setup, moves)
  {G.turn_of(G.play(before, move)) == G.Side.other(G.turn_of(before)) : G.Side}

# Uma jogada valida nunca cai em cima de uma peca do proprio time.
law never_lands_on_own_piece:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +move: G.Action
  for legal: {G.is_legal(G.after(setup, moves), move) == True{} : Bool}
  {G.own_at(G.after(setup, moves), G.to_of(move)) == False{} : Bool}

# ============ CAPTURA ============

# Qualquer peca (aluno ou goleiro) que cai numa casa com peca inimiga captura ela:
# o tabuleiro perde exatamente 1 peca.
law landing_on_enemy_captures:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +move: G.Action
  for legal: {G.is_legal(G.after(setup, moves), move) == True{} : Bool}
  for enemy: {G.enemy_at(G.after(setup, moves), G.to_of(move)) == True{} : Bool}
  +before = G.after(setup, moves)
  {Nat.add(G.piece_count(G.play(before, move)), 1n) == G.piece_count(before) : Nat}

# Cair numa casa vazia nao captura nada: o numero de pecas fica igual.
law empty_square_keeps_pieces:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +move: G.Action
  for legal: {G.is_legal(G.after(setup, moves), move) == True{} : Bool}
  for empty: {G.enemy_at(G.after(setup, moves), G.to_of(move)) == False{} : Bool}
  +before = G.after(setup, moves)
  {G.piece_count(G.play(before, move)) == G.piece_count(before) : Nat}

# Peca capturada sai do jogo de vez: nenhuma jogada, valida ou nao, faz o numero de pecas subir.
law captured_never_return:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for move: G.Action
  +before = G.after(setup, moves)
  {Nat.is_le(G.piece_count(G.play(before, move)), G.piece_count(before)) == True{} : Bool}

# ============ FIM DE JOGO ============

# Capturar o goleiro inimigo: quem jogou vence.
law capturing_teacher_wins:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +move: G.Action
  for legal: {G.is_legal(G.after(setup, moves), move) == True{} : Bool}
  for teacher: {Some{G.to_of(move)} == G.enemy_teacher_square(G.after(setup, moves)) : Maybe<&2, G.Cell>}
  +before = G.after(setup, moves)
  {G.outcome(G.play(before, move)) == G.Winner{G.turn_of(before)} : G.Outcome}

# Qualquer peca que chega no gol inimigo (a casa onde o goleiro dele comecou): quem jogou vence.
law reaching_enemy_home_wins:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +move: G.Action
  for legal: {G.is_legal(G.after(setup, moves), move) == True{} : Bool}
  for home: {G.to_of(move) == G.enemy_home(G.after(setup, moves)) : G.Cell}
  +before = G.after(setup, moves)
  {G.outcome(G.play(before, move)) == G.Winner{G.turn_of(before)} : G.Outcome}

# Empate 1: a mesma posicao (tabuleiro, cartas e vez) apareceu 3 vezes, e ninguem venceu.
law threefold_repetition_draws:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for repeated: {Nat.is_ge(G.repetitions(setup, moves), 3n) == True{} : Bool}
  for no_winner: {G.has_winner(G.after(setup, moves)) == False{} : Bool}
  {G.outcome(G.after(setup, moves)) == G.Draw{} : G.Outcome}

# Empate 2: 20 rodadas seguidas sem nenhuma captura, e ninguem venceu.
law twenty_quiet_turns_draw:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for quiet: {Nat.is_ge(G.quiet_turns(setup, moves), 20n) == True{} : Bool}
  for no_winner: {G.has_winner(G.after(setup, moves)) == False{} : Bool}
  {G.outcome(G.after(setup, moves)) == G.Draw{} : G.Outcome}

# E so isso empata: se deu empate, foi por repeticao ou pelas 20 rodadas.
law draw_only_by_rule:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for drawn: {G.outcome(G.after(setup, moves)) == G.Draw{} : G.Outcome}
  {Bool.or(Nat.is_ge(G.repetitions(setup, moves), 3n), Nat.is_ge(G.quiet_turns(setup, moves), 20n)) == True{} : Bool}

# Jogo terminado nao muda mais: nenhuma jogada e aceita.
law no_moves_after_end:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for move: G.Action
  for over: {G.is_over(G.after(setup, moves)) == True{} : Bool}
  {G.is_legal(G.after(setup, moves), move) == False{} : Bool}

# ============ CARTAS ESCONDIDAS ============

# Na tela, eu vejo as minhas 2 cartas...
law view_shows_own_cards:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +side: G.Side
  {G.View.own(G.view(G.after(setup, moves), side)) == G.own_cards(G.after(setup, moves), side) : List<&2, U32>}

# ...e a carta da mesa.
law view_shows_table_card:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for side: G.Side
  {G.View.table(G.view(G.after(setup, moves), side)) == G.table_card(G.after(setup, moves)) : U32}

# As cartas do inimigo nao aparecem: se elas fossem outras, minha tela seria identica.
law enemy_hand_is_hidden:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +side: G.Side
  for other_cards: List<&2, U32>
  +g = G.after(setup, moves)
  {G.view(G.with_enemy_hand(g, side, other_cards), side) == G.view(g, side) : G.View}

# ============ MULTIPLAYER (P2P) ============

# O codigo de convite sempre volta para o mesmo endereco.
law invite_code_roundtrip:
  for +invite: G.Invite
  {G.Invite.decode(G.Invite.encode(invite)) == Some{invite} : Maybe<G.Invite>}

# Toda mensagem enviada chega igual do outro lado.
law message_roundtrip:
  for +msg: G.Message
  {G.Message.decode(G.Message.encode(msg)) == Some{msg} : Maybe<G.Message>}

# ============ CHANCES NA TELA ============
# (calculadas so com o que o jogador ve, entao nao entregam as cartas do inimigo)

# As partidas simuladas sempre fecham a conta: azul + vermelho + empate = total simulado.
law chances_add_up:
  for setup: G.Setup
  for moves: List<&2, G.Action>
  for viewer: G.Side
  +c = G.chances(G.view(G.after(setup, moves), viewer))
  {G.Chances.total(c) == G.Chances.games(c) : Nat}

# Jogo ja vencido mostra 100% para quem venceu.
law decided_game_is_certain:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for +winner: G.Side
  for viewer: G.Side
  for won: {G.outcome(G.after(setup, moves)) == G.Winner{winner} : G.Outcome}
  +c = G.chances(G.view(G.after(setup, moves), viewer))
  {G.Chances.wins_of(c, winner) == G.Chances.games(c) : Nat}

# Jogo ja empatado mostra 100% de empate.
law drawn_game_is_certain:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for viewer: G.Side
  for drawn: {G.outcome(G.after(setup, moves)) == G.Draw{} : G.Outcome}
  +c = G.chances(G.view(G.after(setup, moves), viewer))
  {G.Chances.draws(c) == G.Chances.games(c) : Nat}

# ============ O QUE A TELA PERGUNTA ============
# A pagina nao decide nada: pergunta ao motor o que um toque na mesa faz e por que a
# partida acabou. Estas leis valem para essas perguntas.

# Um toque na mesa so faz uma jogada valida, e so na vez de quem tocou.
# (qualquer carta escolhida, qualquer botao selecionado, qualquer casa tocada)
law tap_only_plays_legal_moves:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for me: G.Side
  for card: U32
  for sel: U32
  for sq: U32
  {G.click_ok(G.after(setup, moves), me, card, sel, sq) == True{} : Bool}

# Tem motivo de fim exatamente quando a partida acabou.
law ending_only_when_over:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  {G.Ending.is_over(G.ending(G.after(setup, moves))) == G.is_over(G.after(setup, moves)) : Bool}

# Partida que ainda nao acabou nao tem motivo de fim.
law ongoing_has_no_ending:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for playing: {G.outcome(G.after(setup, moves)) == G.Ongoing{} : G.Outcome}
  {G.ending(G.after(setup, moves)) == G.Playing{} : G.Ending}

# ============ O QUE A MESA DESENHA ============
# A mesa 3D desenha a lista G.scene, refeita do tabuleiro a cada vez. Estas leis dizem que ela
# mostra exatamente o jogo: nada a mais, nada a menos, nada lembrado de antes.

# Toda partida começa com 7 peças de cada lado na mesa (6 alunos e o goleiro).
law starts_with_seven_each:
  for +setup: G.Setup
  for side: G.Side
  {G.Tokens.count(G.scene(G.after(setup, Nil{})), side) == 7n : Nat}

# Em cada casa, a mesa mostra exatamente a peça que o jogo tem ali (ou nada).
law table_shows_the_board:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  for sq: G.Cell
  {G.Tokens.code_at(G.scene(G.after(setup, moves)), sq) == G.Pieces.code_at(G.Game.pieces(G.after(setup, moves)), sq) : U32}

# A mesa mostra uma peça por peça do jogo.
law one_token_per_piece:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  {G.Tokens.len(G.scene(G.after(setup, moves))) == G.piece_count(G.after(setup, moves)) : Nat}

# Nunca duas peças desenhadas na mesma casa.
law tokens_never_stack:
  for +setup: G.Setup
  for +moves: List<&2, G.Action>
  {G.Cells.unstacked(G.Tokens.cells(G.scene(G.after(setup, moves)))) == True{} : Bool}

# ============ JOGO ONLINE (PROTOCOLO) ============
# Dois navegadores sorteiam e jogam sem ninguém no meio. A criptografia (hash e travas) roda na
# página e é assumida segura; estas leis provam as decisões em volta dela.

# No sorteio, eu nunca entrego a chave de uma carta minha.
law keys_never_open_my_cards:
  for host: Bool
  for +pos: Nat
  {Bool.and(G.Nats.has(G.Proto.handed(host), pos), G.Nats.has(G.Proto.mine(host), pos)) == False{} : Bool}

# As mãos dos dois nunca dividem uma posição do sorteio.
law hands_never_share_a_position:
  for +pos: Nat
  {Bool.and(G.Nats.has(G.Proto.mine(True{}), pos), G.Nats.has(G.Proto.mine(False{}), pos)) == False{} : Bool}

# Sem prova, o adversário só joga carta que todo mundo já viu (veio da mesa).
law no_proof_only_seen_cards:
  for +opp: G.Opp
  for +card: U32
  for accepted: {G.Verdict.ok(G.Opp.play(opp, card, G.NoProof{})) == True{} : Bool}
  {G.U32s.has(G.Opp.seen(opp), card) == True{} : Bool}

# Carta escondida só é aceita se a chave abrir exatamente essa carta, numa posição que ele
# ainda guarda escondida.
law proof_must_open_that_card:
  for +opp: G.Opp
  for +card: U32
  for +pos: Nat
  for +opened: U32
  for unseen: {G.U32s.has(G.Opp.seen(opp), card) == False{} : Bool}
  for accepted: {G.Verdict.ok(G.Opp.play(opp, card, G.Opened{pos, opened})) == True{} : Bool}
  {Bool.and(G.Nats.has(G.Opp.hidden(opp), pos), U32.is_eq(opened, card)) == True{} : Bool}

# Jogada honesta é sempre aceita: a chave certa de uma posição escondida abre a carta jogada.
law honest_card_accepted:
  for +opp: G.Opp
  for +card: U32
  for +pos: Nat
  for hidden: {G.Nats.has(G.Opp.hidden(opp), pos) == True{} : Bool}
  {G.Verdict.ok(G.Opp.play(opp, card, G.Opened{pos, card})) == True{} : Bool}

# Cada posição prova uma carta uma vez só: depois de usada, ela não está mais escondida.
law each_position_proves_once:
  for +opp: G.Opp
  for +card: U32
  for +pos: Nat
  for +opened: U32
  for unseen: {G.U32s.has(G.Opp.seen(opp), card) == False{} : Bool}
  for accepted: {G.Verdict.ok(G.Opp.play(opp, card, G.Opened{pos, opened})) == True{} : Bool}
  {G.Nats.has(G.Opp.hidden(G.Verdict.opp(G.Opp.play(opp, card, G.Opened{pos, opened}), opp)), pos) == False{} : Bool}

# A carta aceita vai para a mesa.
law accepted_card_goes_to_table:
  for +opp: G.Opp
  for +card: U32
  for +proof: G.Proof
  for accepted: {G.Verdict.ok(G.Opp.play(opp, card, proof)) == True{} : Bool}
  {G.Opp.table(G.Verdict.opp(G.Opp.play(opp, card, proof), opp)) == card : U32}

# Do meu lado: depois de jogar uma carta, eu nunca mais mando a chave dela.
law my_key_goes_once:
  for +held: List<&2, G.Held>
  for +card: U32
  {G.Mine.pos(G.Mine.play(held, card), card) == 99n : Nat}

# ---- a ordem das mensagens e a moeda
# Passos do sorteio: 0 compromisso, 1 revelação da moeda, 2 e 3 o embaralhamento, 4 as chaves;
# 5 é o jogo.

# Cada mensagem do sorteio é aceita na sua vez.
law setup_messages_in_order:
  for host: Bool
  for +step: Nat
  for during: {Nat.is_lt(step, 5n) == True{} : Bool}
  {G.Proto.order(host, step, G.Proto.expected(host, step)) == G.Take{} : G.Order}

# Mensagem do sorteio repetida ou atrasada é trapaça.
law late_setup_message_is_cheat:
  for host: Bool
  for +step: Nat
  for +earlier: Nat
  for before: {Nat.is_lt(earlier, step) == True{} : Bool}
  {G.Proto.order(host, step, G.Proto.expected(host, earlier)) == G.Cheat{} : G.Order}

# Mensagem do sorteio adiantada espera a vez dela.
law early_setup_message_waits:
  for host: Bool
  for +step: Nat
  for +later: Nat
  for after: {Nat.is_lt(step, later) == True{} : Bool}
  for during: {Nat.is_lt(later, 5n) == True{} : Bool}
  {G.Proto.order(host, step, G.Proto.expected(host, later)) == G.Hold{} : G.Order}

# Jogada antes do fim do sorteio é trapaça...
law no_move_before_the_deal:
  for host: Bool
  for +step: Nat
  for during: {Nat.is_lt(step, 5n) == True{} : Bool}
  {G.Proto.order(host, step, 8) == G.Cheat{} : G.Order}

# ...e depois dele é aceita.
law moves_after_the_deal:
  for host: Bool
  for +step: Nat
  for done: {Nat.is_ge(step, 5n) == True{} : Bool}
  {G.Proto.order(host, step, 8) == G.Take{} : G.Order}

# Uma etapa do embaralhamento que cabe ao outro jogador mandar para mim nunca chega de mim
# mesmo: o azul nunca recebe d1 nem d3, o vermelho nunca recebe d2 nem d4.
law blue_never_receives_its_own_shuffle:
  for +step: Nat
  {Bool.and(G.Order.is_cheat(G.Proto.order(True{}, step, 3)), G.Order.is_cheat(G.Proto.order(True{}, step, 5))) == True{} : Bool}

law red_never_receives_its_own_shuffle:
  for +step: Nat
  {Bool.and(G.Order.is_cheat(G.Proto.order(False{}, step, 4)), G.Order.is_cheat(G.Proto.order(False{}, step, 6))) == True{} : Bool}

# A moeda só vale se bater com o compromisso, e só pode ser 0 ou 1.
law coin_must_match_its_commitment:
  for +matches: Bool
  for +bit: U32
  for accepted: {G.Proto.coin_ok(matches, bit) == True{} : Bool}
  {Bool.and(matches, Bool.or(U32.is_eq(bit, 0), U32.is_eq(bit, 1))) == True{} : Bool}

# Moeda honesta (0 ou 1, batendo com o compromisso) é sempre aceita.
law honest_coin_accepted:
  {Bool.and(G.Proto.coin_ok(True{}, 0), G.Proto.coin_ok(True{}, 1)) == True{} : Bool}
