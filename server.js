const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

// ===== 常量 =====
const SUITS = ['♠', '♥', '♦', '♣'];
const RANK_NAMES = ['', 'A', '2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K'];
const RANK_LABELS = {1:'A', 11:'J', 12:'Q', 13:'K'};
const COMP_PAIRS = [[1,13],[2,12],[3,11],[4,10],[5,9],[6,8]];
const DEAL_COUNTS = [8, 7, 7, 5];

function rankLabel(r) { return RANK_LABELS[r] || String(r); }

// ===== 牌堆工具 =====
function createDeck() {
  const deck = [];
  for (let s = 0; s < 4; s++)
    for (let r = 1; r <= 13; r++)
      deck.push({ id: s*13+r-1, rank: r, suit: s });
  return deck;
}
function shuffle(arr) {
  for (let i = arr.length-1; i > 0; i--) {
    const j = Math.floor(Math.random()*(i+1));
    [arr[i],arr[j]] = [arr[j],arr[i]];
  }
  return arr;
}

// ===== 胡牌检测 =====
function countByRank(cards) {
  const c = new Array(14).fill(0);
  for (const card of cards) c[card.rank]++;
  return c;
}

// 检查全部牌能否分成 配组(点数和14)/三张/四张
function checkWin(counts) {
  let totalFan = 0, allValid = true;
  for (const [r1,r2] of COMP_PAIRS) {
    let best = -1;
    for (const g1 of [0,3,4]) {
      if (g1 > counts[r1]) continue;
      for (const g2 of [0,3,4]) {
        if (g2 > counts[r2]) continue;
        if (counts[r1]-g1 === counts[r2]-g2) {
          let fan = (g1===3?1:0)+(g1===4?2:0)+(g2===3?1:0)+(g2===4?2:0);
          if (fan > best) best = fan;
        }
      }
    }
    if (best < 0) { allValid = false; break; }
    totalFan += best;
  }
  if (allValid) {
    let best7 = -1;
    for (const g7 of [0,3,4]) {
      if (g7 > counts[7]) continue;
      if ((counts[7]-g7)%2 === 0) {
        let fan = (g7===3?1:0)+(g7===4?2:0);
        if (fan > best7) best7 = fan;
      }
    }
    if (best7 < 0) return { canWin:false, fan:0 };
    totalFan += best7;
  }
  if (!allValid) return { canWin:false, fan:0 };
  return { canWin:true, fan:Math.min(totalFan,3) };
}

function getAllCards(player, tableCard) {
  const cards = [...player.hand];
  for (const g of player.front) cards.push(...g.cards);
  if (tableCard) cards.push(tableCard);
  return cards;
}

function canWinWith(player, tableCard) {
  return checkWin(countByRank(getAllCards(player, tableCard)));
}

function canBaogi(hand) {
  const counts = countByRank(hand);
  for (let r = 1; r <= 13; r++) {
    if (counts[r] > 0) {
      counts[r]--;
      if (checkWin(counts).canWin) { counts[r]++; return true; }
      counts[r]++;
    }
  }
  return false;
}

function findTriples(hand) {
  const counts = countByRank(hand);
  const triples = [];
  for (let r = 1; r <= 13; r++) if (counts[r] >= 3) triples.push(r);
  return triples;
}

function findEatable(hand, tableCard) {
  const target = 14 - tableCard.rank;
  return hand.filter(c => c.rank === target);
}

function hasGrabPair(hand, tableCard) {
  return hand.filter(c => c.rank === tableCard.rank).length >= 2;
}

function canDig(player) {
  if (!player.lastDrawn) return false;
  for (const g of player.front) {
    if (g.type !== '吃' && g.cards[0].rank === player.lastDrawn.rank) return true;
  }
  return false;
}

// ===== 游戏状态 =====
const rooms = {};

function createGame(roomId) {
  return {
    roomId, phase:'lobby', players:[],
    deck:[], tableCard:null, tableSource:null,
    currentPlayer:0, stealTurn:0, declareTurn:0, subState:null,
    messages:[], winner:null, scores:null, fangpaoId:null, winType:null,
  };
}

function dealCards(game) {
  game.deck = shuffle(createDeck());
  const n = game.players.length;
  for (let i = 0; i < n; i++) {
    game.players[i].hand = game.deck.splice(0, DEAL_COUNTS[i]);
    game.players[i].front = [];
    game.players[i].stealDone = false;
    game.players[i].baogi = false;
    game.players[i].lastDrawn = null;
    game.players[i].winFan = 0;
  }
}

function addMsg(game, msg) {
  game.messages.push(msg);
  if (game.messages.length > 30) game.messages.shift();
}

function nextStealTurn(game) {
  const n = game.players.length;
  do {
    game.stealTurn++;
    if (game.stealTurn >= n) {
      // 偷起结束，进入宣告
      startDeclaring(game);
      return;
    }
  } while (findTriples(game.players[game.stealTurn].hand).length === 0);
  // 如果当前玩家没有三张，自动跳过
  broadcastState(game);
}

function startDeclaring(game) {
  game.phase = 'declaring';
  game.declareTurn = -1;
  // 检查天胡
  const a = game.players[0];
  const tianhu = checkWin(countByRank(getAllCards(a, null)));
  if (tianhu.canWin) {
    game.winner = 0;
    game.winType = 'tianhu';
    game.players[0].winFan = tianhu.fan;
    endGame(game);
    return;
  }
  // 进入爆起宣告，逐个玩家
  game.declareTurn = 0;
  // 自动跳过不能爆起的玩家
  advanceDeclare(game);
}

function advanceDeclare(game) {
  const n = game.players.length;
  while (game.declareTurn < n) {
    if (canBaogi(game.players[game.declareTurn].hand)) {
      broadcastState(game);
      return;
    }
    game.declareTurn++;
  }
  // 宣告结束，开始出牌
  startPlaying(game);
}

function startPlaying(game) {
  game.phase = 'first_play';
  game.currentPlayer = 0;
  game.subState = null;
  addMsg(game, '偷起/宣告阶段结束，玩家A先出牌');
  broadcastState(game);
}

function startNormalPlay(game) {
  game.phase = 'playing';
  game.currentPlayer = 1; // b先看牌
  game.subState = null;
  broadcastState(game);
}

function nextPlayTurn(game) {
  const n = game.players.length;
  game.currentPlayer = (game.currentPlayer + 1) % n;
  game.subState = null;
  // 检查牌堆耗尽且当前玩家无法行动 → 流局
  if (game.deck.length === 0 && game.tableCard) {
    const acts = getAvailableActions(game, game.currentPlayer);
    const hasRealAction = acts.some(a => !a.auto);
    if (!hasRealAction) {
      addMsg(game, '牌堆已空，本局作废');
      game.phase = 'ended';
      game.winner = -1;
      game.scores = {};
      for (let i = 0; i < n; i++) game.scores[i] = 0;
      broadcastState(game);
      return;
    }
  }
  broadcastState(game);
}

function checkDeckEmpty(game) {
  if (game.deck.length === 0) {
    addMsg(game, '牌堆已空，本局作废');
    game.phase = 'ended';
    game.winner = -1;
    game.scores = {};
    for (let i = 0; i < game.players.length; i++) game.scores[i] = 0;
    broadcastState(game);
    return true;
  }
  return false;
}

function endGame(game) {
  game.phase = 'ended';
  const winner = game.players[game.winner];
  const fan = winner.winFan || 0;
  let base = fan === 0 ? 1 : fan === 1 ? 2 : fan === 2 ? 4 : 8;
  if (winner.baogi) base += 1;

  game.scores = {};
  const n = game.players.length;
  const losers = n - 1;

  if (game.winType === 'fangpao') {
    for (let i = 0; i < n; i++) {
      if (i === game.winner) game.scores[i] = base * losers;
      else if (i === game.fangpaoId) game.scores[i] = -base * losers;
      else game.scores[i] = 0;
    }
  } else {
    for (let i = 0; i < n; i++) {
      if (i === game.winner) game.scores[i] = base * losers;
      else game.scores[i] = -base;
    }
  }

  const fanName = fan === 0 ? '小胡' : fan >= 3 ? '满贯' : fan + '番';
  const baogiName = winner.baogi ? '+爆起' : '';
  addMsg(game, `${winner.name} 胡牌！${fanName}${baogiName} 得${base * losers}分`);

  broadcastState(game);
}

// ===== 动作处理 =====
function handleAction(game, idx, msg) {
  const player = game.players[idx];
  const a = msg.action;

  if (a === 'steal') {
    const rank = msg.rank;
    const triple = player.hand.filter(c => c.rank === rank);
    if (triple.length < 3) return sendError(player.ws, '没有三张同点数的牌');
    // 移除三张
    player.hand = player.hand.filter(c => c.rank !== rank);
    // 放面前
    player.front.push({ cards: triple.slice(0,3), type: '偷' });
    // 摸一张
    if (game.deck.length > 0) player.hand.push(game.deck.shift());
    player.stealDone = true;
    addMsg(game, `${player.name} 偷起了三个${rankLabel(rank)}`);
    nextStealTurn(game);
  }
  else if (a === 'skipSteal') {
    player.stealDone = true;
    nextStealTurn(game);
  }
  else if (a === 'declareBaogi') {
    player.baogi = true;
    addMsg(game, `${player.name} 宣布爆起`);
    if (game.phase === 'a_baogi') { startNormalPlay(game); return; }
    game.declareTurn++;
    advanceDeclare(game);
  }
  else if (a === 'skipBaogi') {
    if (game.phase === 'a_baogi') { startNormalPlay(game); return; }
    game.declareTurn++;
    advanceDeclare(game);
  }
  else if (a === 'playFirst') {
    const cardId = msg.cardId;
    const ci = player.hand.findIndex(c => c.id === cardId);
    if (ci < 0) return sendError(player.ws, '没有这张牌');
    const card = player.hand.splice(ci, 1)[0];
    game.tableCard = card;
    game.tableSource = 'play';
    addMsg(game, `${player.name} 打出 ${SUITS[card.suit]}${rankLabel(card.rank)}`);
    // 检查A是否可以爆起
    if (canBaogi(player.hand)) {
      game.phase = 'a_baogi';
      broadcastState(game);
    } else {
      startNormalPlay(game);
    }
  }
  else if (a === 'win') {
    const result = canWinWith(player, game.tableCard);
    if (!result.canWin) return sendError(player.ws, '不能胡牌');
    player.winFan = result.fan;
    game.winner = idx;
    if (game.tableSource === 'play') {
      game.winType = 'fangpao';
      // 放炮者是打出这张牌的人
      game.fangpaoId = (idx - 1 + game.players.length) % game.players.length;
    } else {
      game.winType = 'deck';
    }
    addMsg(game, `${player.name} 胡牌！`);
    endGame(game);
  }
  else if (a === 'grab') {
    if (!game.tableCard || !hasGrabPair(player.hand, game.tableCard))
      return sendError(player.ws, '不能抓牌');
    const rank = game.tableCard.rank;
    // 移除手牌中的2张同点数牌
    let removed = 0;
    const pair = [];
    player.hand = player.hand.filter(c => {
      if (c.rank === rank && removed < 2) { removed++; pair.push(c); return false; }
      return true;
    });
    player.front.push({ cards: [...pair, game.tableCard], type: '抓' });
    game.tableCard = null;
    // 摸一张
    if (checkDeckEmpty(game)) return;
    const drawn = game.deck.shift();
    player.hand.push(drawn);
    player.lastDrawn = drawn;
    addMsg(game, `${player.name} 抓了三个${rankLabel(rank)}，摸了一张牌`);
    // 检查能否胡
    const winResult = canWinWith(player, null);
    if (winResult.canWin) {
      game.subState = 'after_grab';
      addMsg(game, `${player.name} 可以抓轴胡！`);
      broadcastState(game);
    } else if (canDig(player)) {
      game.subState = 'after_grab';
      broadcastState(game);
    } else {
      game.subState = 'must_play';
      broadcastState(game);
    }
  }
  else if (a === 'dig') {
    if (!player.lastDrawn || !canDig(player))
      return sendError(player.ws, '不能扒');
    // 找到匹配的同点数组
    const mg = player.front.find(g => g.type !== '吃' && g.cards[0].rank === player.lastDrawn.rank);
    // 从手牌移除lastDrawn
    player.hand = player.hand.filter(c => c.id !== player.lastDrawn.id);
    // 加入面前组
    mg.cards.push(player.lastDrawn);
    mg.type = '扒';
    addMsg(game, `${player.name} 扒了 ${SUITS[player.lastDrawn.suit]}${rankLabel(player.lastDrawn.rank)}`);
    // 摸一张
    if (checkDeckEmpty(game)) return;
    const drawn = game.deck.shift();
    player.hand.push(drawn);
    player.lastDrawn = drawn;
    // 再次检查
    const winResult = canWinWith(player, null);
    if (winResult.canWin) {
      game.subState = 'after_grab';
      broadcastState(game);
    } else if (canDig(player)) {
      game.subState = 'after_grab';
      broadcastState(game);
    } else {
      game.subState = 'must_play';
      broadcastState(game);
    }
  }
  else if (a === 'skipDig' || a === 'skipPlay') {
    game.subState = 'must_play';
    broadcastState(game);
  }
  else if (a === 'eat') {
    const cardId = msg.cardId;
    const ci = player.hand.findIndex(c => c.id === cardId);
    if (ci < 0) return sendError(player.ws, '没有这张牌');
    if (!game.tableCard || 14 - game.tableCard.rank !== player.hand[ci].rank)
      return sendError(player.ws, '不能吃这张牌');
    const tc = game.tableCard;
    const eatCard = player.hand.splice(ci, 1)[0];
    player.front.push({ cards: [eatCard, tc], type: '吃' });
    game.tableCard = null;
    addMsg(game, `${player.name} 吃了 ${SUITS[eatCard.suit]}${rankLabel(eatCard.rank)}+${SUITS[tc.suit]}${rankLabel(tc.rank)}`);
    game.subState = 'must_play';
    broadcastState(game);
  }
  else if (a === 'flip') {
    if (game.deck.length === 0) {
      addMsg(game, '牌堆已空，本局作废');
      game.phase = 'ended';
      game.winner = -1;
      game.scores = {};
      for (let i = 0; i < game.players.length; i++) game.scores[i] = 0;
      broadcastState(game);
      return;
    }
    const flipped = game.deck.shift();
    game.tableCard = flipped;
    game.tableSource = 'flip';
    addMsg(game, `${player.name} 翻出 ${SUITS[flipped.suit]}${rankLabel(flipped.rank)}`);
    nextPlayTurn(game);
  }
  else if (a === 'play') {
    const cardId = msg.cardId;
    const ci = player.hand.findIndex(c => c.id === cardId);
    if (ci < 0) return sendError(player.ws, '没有这张牌');
    const card = player.hand.splice(ci, 1)[0];
    game.tableCard = card;
    game.tableSource = 'play';
    player.lastDrawn = null;
    addMsg(game, `${player.name} 打出 ${SUITS[card.suit]}${rankLabel(card.rank)}`);
    nextPlayTurn(game);
  }
  else if (a === 'winGrab') {
    // 抓轴胡
    const result = canWinWith(player, null);
    if (!result.canWin) return sendError(player.ws, '不能胡牌');
    player.winFan = result.fan;
    game.winner = idx;
    game.winType = 'grab';
    addMsg(game, `${player.name} 抓轴胡！`);
    endGame(game);
  }
}

// ===== 状态同步 =====
function getAvailableActions(game, idx) {
  const player = game.players[idx];
  const actions = [];

  if (game.phase === 'stealing' && game.stealTurn === idx) {
    const triples = findTriples(player.hand);
    if (triples.length === 0) return [{action:'skipSteal', auto:true}];
    for (const r of triples) actions.push({action:'steal', rank:r, label:`偷起 三个${rankLabel(r)}`});
    actions.push({action:'skipSteal', label:'忽略'});
  }
  else if (game.phase === 'declaring' && game.declareTurn === idx) {
    if (canBaogi(player.hand)) {
      actions.push({action:'declareBaogi', label:'爆起'});
      actions.push({action:'skipBaogi', label:'忽略'});
    } else {
      return [{action:'skipBaogi', auto:true}];
    }
  }
  else if (game.phase === 'a_baogi' && idx === 0) {
    if (canBaogi(player.hand)) {
      actions.push({action:'declareBaogi', label:'爆起'});
      actions.push({action:'skipBaogi', label:'忽略'});
    } else {
      return [{action:'skipBaogi', auto:true}];
    }
  }
  else if (game.phase === 'first_play' && game.currentPlayer === idx) {
    actions.push({action:'playFirst', label:'选择一张牌打出'});
  }
  else if (game.phase === 'playing' && game.currentPlayer === idx) {
    if (game.subState === null) {
      if (game.tableCard) {
        const wr = canWinWith(player, game.tableCard);
        if (wr.canWin) actions.push({action:'win', label:'胡牌', fan:wr.fan});
        if (hasGrabPair(player.hand, game.tableCard))
          actions.push({action:'grab', label:'抓牌'});
        if (player.hand.length >= 2) {
          const eatable = findEatable(player.hand, game.tableCard);
          for (const c of eatable)
            actions.push({action:'eat', cardId:c.id, label:`吃 ${SUITS[c.suit]}${rankLabel(c.rank)}`});
        }
        if (game.deck.length > 0)
          actions.push({action:'flip', label:'翻牌'});
      }
    } else if (game.subState === 'after_grab') {
      const wr = canWinWith(player, null);
      if (wr.canWin) actions.push({action:'winGrab', label:'抓轴胡', fan:wr.fan});
      if (canDig(player)) actions.push({action:'dig', label:'扒'});
      actions.push({action:'skipDig', label:'不扒，出牌'});
    } else if (game.subState === 'must_play') {
      actions.push({action:'play', label:'选择一张牌打出'});
    }
  }

  return actions;
}

function getView(game, idx) {
  const player = game.players[idx];
  return {
    phase: game.phase,
    roomId: game.roomId,
    currentPlayer: game.currentPlayer,
    stealTurn: game.stealTurn,
    declareTurn: game.declareTurn,
    tableCard: game.tableCard ? {...game.tableCard, label: rankLabel(game.tableCard.rank), suitChar: SUITS[game.tableCard.suit]} : null,
    tableSource: game.tableSource,
    deckSize: game.deck.length,
    subState: game.subState,
    myHand: player.hand.map(c => ({...c, label: rankLabel(c.rank), suitChar: SUITS[c.suit]})),
    myFront: player.front.map(g => ({
      type: g.type,
      cards: g.cards.map(c => ({...c, label: rankLabel(c.rank), suitChar: SUITS[c.suit]}))
    })),
    lastDrawn: player.lastDrawn ? {...player.lastDrawn, label: rankLabel(player.lastDrawn.rank), suitChar: SUITS[player.lastDrawn.suit]} : null,
    players: game.players.map((p,i) => ({
      id:i, name:p.name, handSize:p.hand.length,
      front: p.front.map(g => ({
        type:g.type,
        cards: g.cards.map(c => ({...c, label:rankLabel(c.rank), suitChar:SUITS[c.suit]}))
      })),
      stealDone:p.stealDone, baogi:p.baogi, winFan:p.winFan||0,
      isMe:i===idx, isHost:i===0,
    })),
    actions: getAvailableActions(game, idx),
    messages: game.messages.slice(-12),
    winner: game.winner,
    scores: game.scores,
    winType: game.winType,
    myId: idx,
  };
}

function broadcastState(game) {
  for (let i = 0; i < game.players.length; i++) {
    if (game.players[i].ws && game.players[i].ws.readyState === 1) {
      game.players[i].ws.send(JSON.stringify({type:'state', state: getView(game, i)}));
    }
  }
}

function sendError(ws, msg) {
  if (ws && ws.readyState === 1)
    ws.send(JSON.stringify({type:'error', msg}));
}

// ===== WebSocket 服务器 =====
const server = http.createServer((req, res) => {
  if (req.url === '/' || req.url === '/index.html') {
    res.writeHead(200, {
      'Content-Type':'text/html; charset=utf-8',
      'Cache-Control':'no-cache, no-store, must-revalidate'
    });
    res.end(fs.readFileSync(path.join(__dirname, 'index.html')));
  } else if (req.url === '/favicon.ico') {
    res.writeHead(204);
    res.end();
  } else {
    res.writeHead(404);
    res.end('Not found');
  }
});

const wss = new WebSocketServer({ server });

wss.on('connection', (ws) => {
  let myRoom = null, myIdx = -1;

  ws.on('message', (raw) => {
    let msg;
    try { msg = JSON.parse(raw); } catch { return; }
    try {
    if (msg.type === 'create') {
      const roomId = String(Math.floor(Math.random()*9000)+1000);
      const game = createGame(roomId);
      game.players.push({
        id:0, name:msg.name||'玩家A', ws, hand:[], front:[],
        stealDone:false, baogi:false, lastDrawn:null, winFan:0,
      });
      rooms[roomId] = game;
      myRoom = roomId; myIdx = 0;
      ws.send(JSON.stringify({type:'created', roomId}));
      broadcastState(game);
    }
    else if (msg.type === 'join') {
      const game = rooms[msg.roomId];
      if (!game) return ws.send(JSON.stringify({type:'error', msg:'房间不存在'}));
      if (game.phase !== 'lobby') return ws.send(JSON.stringify({type:'error', msg:'游戏已开始'}));
      if (game.players.length >= 4) return ws.send(JSON.stringify({type:'error', msg:'房间已满'}));
      myIdx = game.players.length;
      game.players.push({
        id:myIdx, name:msg.name||`玩家${'ABCD'[myIdx]}`, ws, hand:[], front:[],
        stealDone:false, baogi:false, lastDrawn:null, winFan:0,
      });
      myRoom = msg.roomId;
      broadcastState(game);
    }
    else if (msg.type === 'start') {
      const game = rooms[myRoom];
      if (!game || myIdx !== 0) return sendError(ws, '只有房主能开始');
      if (game.players.length < 2) return sendError(ws, '至少需要2人');
      dealCards(game);
      game.phase = 'stealing';
      game.stealTurn = 0;
      // 自动跳过没有三张的玩家
      while (game.stealTurn < game.players.length &&
             findTriples(game.players[game.stealTurn].hand).length === 0) {
        game.players[game.stealTurn].stealDone = true;
        game.stealTurn++;
      }
      if (game.stealTurn >= game.players.length) {
        startDeclaring(game);
      } else {
        addMsg(game, '游戏开始！偷起阶段');
        broadcastState(game);
      }
    }
    else if (msg.type === 'action') {
      const game = rooms[myRoom];
      if (!game) return;
      // 自动跳过处理
      if (msg.action === 'skipSteal' && msg.auto) {
        game.players[myIdx].stealDone = true;
        nextStealTurn(game);
        return;
      }
      if (msg.action === 'skipBaogi' && msg.auto) {
        if (game.phase === 'a_baogi') { startNormalPlay(game); return; }
        game.declareTurn++;
        advanceDeclare(game);
        return;
      }
      handleAction(game, myIdx, msg);
    }
    else if (msg.type === 'restart') {
      const game = rooms[myRoom];
      if (!game || myIdx !== 0) return;
      const oldPlayers = game.players.map(p => ({name:p.name, ws:p.ws}));
      const newGame = createGame(game.roomId);
      for (const p of oldPlayers) {
        newGame.players.push({
          id:newGame.players.length, name:p.name, ws:p.ws, hand:[], front:[],
          stealDone:false, baogi:false, lastDrawn:null, winFan:0,
        });
      }
      rooms[game.roomId] = newGame;
      broadcastState(newGame);
    }
    } catch(e) {
      console.error('消息处理错误:', e.message, e.stack);
      sendError(ws, '服务器错误: ' + e.message);
    }
  });

  ws.on('close', () => {
    if (myRoom && rooms[myRoom]) {
      addMsg(rooms[myRoom], `玩家断开连接`);
      broadcastState(rooms[myRoom]);
    }
  });
});

const PORT = process.env.PORT || 8080;
const HOST = '0.0.0.0';
server.listen(PORT, HOST, () => {
  console.log(`棋牌服务已启动: http://localhost:${PORT}`);
  console.log(`手机访问: http://你的公网地址:${PORT}`);
  console.log('按 Ctrl+C 停止');
});
