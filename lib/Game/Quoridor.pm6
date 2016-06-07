unit module Game::Quoridor;
use v6;

my class X::Game::Quoridor is Exception {
}

my class X::Game::Quoridor::GameError is X::Game::Quoridor {
    method message { "game error" }
}

my class X::Game::Quoridor::WrongNumberOfPlayers is X::Game::Quoridor::GameError {
    method message() { callsame() ~ ": bad number of players" }
}

my class X::Game::Quoridor::PlayerNumberTaken is X::Game::Quoridor::GameError {
    method message() { callsame() ~ ": player number is taken" }
}

my class X::Game::Quoridor::PlayerMistake is X::Game::Quoridor {
}

my class X::Game::Quoridor::IllegalMove is X::Game::Quoridor::PlayerMistake {
    method message() { "illegal move" }
}

my class X::Game::Quoridor::GameOver is X::Game::Quoridor::PlayerMistake {
    method message() { callsame() ~ ": game over, no more moves" }
}

my class X::Game::Quoridor::SquareOccupied is X::Game::Quoridor::IllegalMove {
    method message() { callsame() ~ ": square occupied" }
}

my class X::Game::Quoridor::IllegalHop is X::Game::Quoridor::IllegalMove {
    method message() { callsame() ~ ": illegal hop" }
}

my class X::Game::Quoridor::NoMove is X::Game::Quoridor::IllegalMove {
    method message() { callsame() ~ ": no move" }
}

my class X::Game::Quoridor::BlockedBy is X::Game::Quoridor::IllegalMove {
    has Str $.what;
    method message() { callsame() ~ ": blocked by " ~ $!what }
}

my class X::Game::Quoridor::WallSlotOccupied is X::Game::Quoridor::IllegalMove {
    method message() { callsame() ~ ": wall slot is occupied" }
}

subset SquarePosition of Str where /^ <[a .. i]> <[1 .. 9]> $/;
subset WallPosition of Str where /^ <[a .. j]> <[1 .. 8]> <[h v]> $/;
subset WinningPosition of Str where 'a' | 'j' | '1' | '8';

my multi to-num(Str:D $x where any('a' .. 'i')) { $x.ord - 'a'.ord }
my multi to-num(Str:D $x where any('1' .. '9')) { $x - 1 }

my sub infix:<delta>(SquarePosition:D $from, SquarePosition:D $to) returns Int:D is equiv(&infix:<->) is export {
    my ($from_c, $to_c) = ($from, $to).map: { [.comb.map({ to-num($_) })] };
    [+] ($from_c.list Z- $to_c.list).map: *.abs;
}

my sub infix:<a+>(Str:D $x where any('a' .. 'i'), Int:D $y) is equiv(&infix:<+>) is export { ($x.ord + $y).chr }
my sub infix:<a->(Str:D $x where any('a' .. 'i'), Int:D $y) is equiv(&infix:<->) is export { ($x.ord - $y).chr }

my sub neighbors(SquarePosition:D $s) is export {
    my ($a, $b) = $s.comb;
    ($a a+ 1 ~ $b, $a a- 1 ~ $b, $a ~ $b + 1, $a ~ $b - 1).grep: SquarePosition:D;
}

my sub wall-blocks(WallPosition:D $w) is export {
    my ($c, $r, $d) = $w.comb;
    my $left  = $c a+ 1;
    my $right = $c;
    my $top   = $r;
    my $bot   = $r + 1;

    if $d eq 'h' {
        ($left ~ $top, $left ~ $bot), ($right ~ $top, $right ~ $bot);
    }
    else {
        ($left ~ $top, $right ~ $top), ($left ~ $bot, $right ~ $bot);
    }
}

class Board {
    has $.players;

    has $.turn = 0;
    has SquarePosition @.pawns;
    has WinningPosition @.winning-positions;
    has SetHash $.walls = SetHash.new;
    has $.winner;

    has SetHash %.blocked;

    submethod BUILD(:$!players = 2) {
        if $!players == 2 {
            @!pawns = <e9 e1>;
            @!winning-positions = <1 9>;
        }
        elsif $!players == 4 {
            @!pawns = <e9 e1 i5 a5>;
            @!winning-positions = <1 9 a i>;
        }
        else {
            die X::Game::Quoridor::BadNumberOfPlayers.new;
        }
    }

    method has-winner() returns Bool:D { $.winner.defined }

    method this-player() returns Int:D {
        $!turn + 1
    }

    method next-turn() {
        $!turn = ($!turn + 1) % $!players;
    }

    multi method move(Board:D: SquarePosition $to) {
        die X::Game::Quoridor::GameOver.new if $.has-winner;
        die X::Game::Quoridor::SquareOccupied.new if $to ~~ any(|@!pawns);

        my $here := @!pawns[ $!turn ];

        my $delta = $here delta $to;
        if $delta == 0 {
            die X::Game::Quoridor::NoMove.new;
        }
        elsif $delta > 1 {
            my @open-list = $here;
            my $hoppable-pawns = set gather while my $try = @open-list.shift {
                for neighbors($try) -> $sq {
                    if !%!blocked{$here}{$sq} && $sq eq any(|@!pawns) {
                        take $sq;
                        @open-list.push: $sq;
                    }
                }
            }

            my $open-hop-squares = set $hoppable-pawns.keys.map({ neighbors($_) }).grep({
                !%.blocked{$here}{$_} && $_ ne any(|@!pawns)
            });

            die X::Game::Quoridor::IllegalHop.new unless $here ∈ $open-hop-squares;
        }
        else {
            die X::Game::Quoridor::BlockedBy.new(:what<wall>)
            if %!blocked{$here}{$to};
            die X::Game::Quoridor::BlockedBy.new(:what<pawn>)
            if $to eq any(|@!pawns);
        }

        $here = $to;

        my $winning-position = @.winning-position[ $!turn ];
        if $here ~~ /^ $winning-position $/ {
            $!winner = $!turn;
        }
        else {
            self.next-turn;
        }
    }

    multi method move(Board:D: WallPosition $at) {
        die X::Game::Quoridor::GameOver.new if $.has-winner;
        die X::Game::Quoridor::WallSlotOccupied.new
        if $.walls ∋ $at.subst(/.$/, 'v');
        die X::Game::Quoridor::WallSlotOccupied.new
        if $.walls ∋ $at.subst(/.$/, 'h');

        my ($c, $r, $d) = $at.comb;

        if $d eq 'h' {
            die X::Game::Quoridor::WallSlotOccupied.new
            if $.walls ∋ [~] $c, $r + 1, $d;
            die X::Game::Quoridor::WallSlotOccupied.new
            if $.walls ∋ [~] $c, $r - 1, $d;
        }
        else {
            die X::Game::Quoridor::WallSlotOccupied.new
            if $.walls ∋ [~] $c a+ 1, $r, $d;
            die X::Game::Quoridor::WallSlotOccupied.new
            if $.walls ∋ [~] $c a- 1, $r, $d;
        }

        $.walls{ $at }++;
        my @blocks = wall-blocks($at);
        for @blocks -> $block {
            note "WALL $block[0] <-> $block[1]\n";
            %!blocked{ $block[0] } //= SetHash.new;
            %!blocked{ $block[0] }{ $block[1] }++;
            %!blocked{ $block[1] } //= SetHash.new;
            %!blocked{ $block[1] }{ $block[0] }++;
        }

        self.next-turn;
    }

    method text-board(Board:D:) {
        my $out = "   a b c d e f g h i\n  /-+-+-+-+-+-+-+-+-\\\n";
        for '1' .. '9' -> $r {
            $out ~= $r ~ ' ';
            for 'a' .. 'i' -> $c {
                if $c eq 'a' || $!walls ∋ $c ~ $r ~ 'v' || $!walls ∋ $c ~ $r - 1 ~ 'v' {
                    $out ~= '|';
                }
                else {
                    $out ~= ' ';
                }

                $out ~= @!pawns.grep($c ~ $r, :k).map({ $_ + 1 }).first // ' ';
            }
            $out ~= "|\n";

            if $r ne '9' {
                $out ~= '  +';
                for 'a' .. 'i' -> $c {
                    my $n = $c eq 'i' ?? '+' !! '+';
                    if $!walls ∋ ($c ~ $r ~ 'h') || $!walls ∋ ($c a- 1 ~ $r ~ 'h') {
                        $out ~= "-$n";
                    }
                    else {
                        $out ~= " $n";
                    }
                }
                $out ~= "\n";
            }
        }
        $out ~= "  \\-+-+-+-+-+-+-+-+-/\n";
        $out;
    }
}

class Server {
    has Str $.host = 'localhost';
    has Int $.port = 9999;

    has SetHash $!names;
    has %!games;
    has @!finished-games;

    my class Game { ... }

    my class Client {
        has Str $.name;
        has Str $.type;
        has Int $.num;
        has Game $.game;
        has $.conn;

        method title() { "{$.type.tc} #$!num" }

        method says($message) { qq[$.title says, "$message"] }
        method acts($message) { qq[$.title $message] }

        method tell($message)     { $!conn.print("$message\n") }
        method tell-error($error) { self.tell("!!! $error") }
        method tell-ok($ok)       { self.tell("OK $ok") }

        method hello($name) {
            with $.name {
                self.tell-error('no more hellos');
            }
            else {
                $.name = $name;
                self.tell-ok('name set');
            }
        }

        method join($game, Int(Cool) $number) {
            $!game = $game;
            $!type = 'player';
            $!num  = $number;
        }

        method watch($game) {
            $!game = $game;
            $!type = 'watcher';
        }

        method leave() {
            $!game = Nil;
            $!type = Nil;
            $!num  = Nil;
        }

        method disconnect() {
            self.tell-ok('bye');
            $.conn.close;
        }
    }

    subset Watcher of Client where *.type eq 'watcher';
    subset Player of Client where *.type eq 'player';

    my class Game {
        has Str $.name;
        has Int $.players where 2|4;
        has Str @.player-names;
        has Str $.winner-name;
        has Board $.board;
        has $.ready = False;
        has $.finished = False;

        has SetHash $!open-players;
        has Watcher @!watchers;
        has Player @!players;

        submethod BUILD(:$!name, :$!players) {
            $!board = Board.new(:$!players);
        }

        method status() {
            if    not $!ready    { "being setup" }
            elsif not $!finished { "in progress" }
            else                 { "finishing up" }
        }

        method announce($text, Set() :$exclude) {
            for |@!watchers, @!players -> $client {
                next if $exclude ∋ $client.name;
                $client.tell($text);
            }
        }

        method count-active-players() returns Int:D {
            @!players.grep({ .defined }).elems
        }

        multi method join($client, '*') {
            my $number = $!open-players.pick;
            callwith($client, $number);
        }

        multi method join($client, Int(Cool) $number) {
            if $!open-players ∋ $number {
                $!open-players{ $number }--;
            }
            else {
                die X::Game::Quoridor::PlayerNumberTaken.new;
            }

            $client.join(self, $number);
            @!players[ $number ] = $client;
            @!player-names[ $number ] = $client.name;

            self.start-game if $!open-players.elems == 0;
        }

        method start-game() {
            $!ready = True;
            self.announce-turn;
        }

        method announce-turn() {
            # make sure we skip resigned players
            until @!players[ $.board.turn ].defined {
                $.board.next-turn;
            }

            @!players[ $.board.turn ].tell("GO");
        }

        multi method move(Player $player, SquarePosition $move) {
            if @!players[ $.board.turn ] === $player {
                $.board.move($move);
                self.announce( $player.acts($move) );

                if $.board.has-winner {
                    self.end-game;
                }
                else {
                    self.announce-turn;
                }
            }
            else {
                die X::Game::Quoridor::WaitYourTurn.new;
            }
        }

        multi method move(Player $player, WallPosition $move) {
            if @!players[ $.board.turn ] === $player {
                $.board.move($move);
                self.announce( $player.acts($move) );
                self.announce-turn;
            }
            else {
                die X::Game::Quoridor::WaitYourTurn.new;
            }
        }

        method watch($client) {
            $client.watch(self);
            push @!watchers, $client;
        }

        method comment($client, $text) {
            self.announce(
                $client.says($text),
                exclude => $client.name,
            );
        }

        method end-game() {
            my $winner := @!players[ $.board.winner ];
            self.announce( $winner.acts("WINS") );

            $!winner-name = $winner.name;
            $!finished = True;

            .leave for flat @!watchers, @!players;

            @!watchers = ();
            @!players  = ();
        }

        multi method leave(Watcher $client) {
            @!watchers .= grep: { $_ !=== $client };
            $client.leave;
        }

        multi method leave(Player $client) {
            self.announce( $client.acts("RESIGNS") );
            if $.count-active-players - 1 == 1 {
                my $winner = @!players.first: { .defined };
                self.announce( $winner.acts("WINS") );

                $!winner-name = $winner.name;
                $!finished = True;
            }

            @!players .= grep: { $_ !=== $client };
            $client.leave;
        }
    }

    my grammar ClientCommands {
        rule TOP {
            || <hello>
            || <start-game>
            || <join-game>
            || <watch-game>
            || <quit>
        }

        rule hello      { hello <name> }
        rule start-game { start <players> <name> }
        rule join-game  { join <number> <name> }
        rule watch-game { watch <name> }
        rule quit       { quit }

        token players { 2 | 4 }
        token name    { <[ \w - ]>+ }
        token number  { <[ 1 .. 4 * ]> }
    }

    my class ClientActions {
        has $.client;
        has $.server;

        method hello($/) {
            $.server.hello($.client, $/<name>);
        }

        method start-game($/) {
            $.server.start-game($.client, $/<players>, $/<name>);
        }

        method join-game($/) {
            $.server.join-game($.client, $/<number>, $/<name>);
        }

        method watch-game($/) {
            $.server.watch-game($.client, $/<name>);
        }

        method quit($/) {
            $.server.quit($.client);
        }
    }

    my grammar WatcherCommands {
        rule TOP {
            || <comment>
            || <leave-game>
            || <quit>
        }

        rule comment    { '#' <text> }
        rule leave-game { leave }
        rule quit       { quit }

        token text { .* }
    }

    my class WatcherActions {
        has $.client;
        has $.server;

        method comment($/) {
            $.server.comment($.client, $/<text>);
        }

        method leave-game($/) {
            $.server.leave-game($.client);
        }

        method quit($/) {
            $.server.quit($.client);
        }
    }

    my grammar PlayerCommands {
        rule TOP {
            || <move-pawn>
            || <set-wall>
            || <comment>
            || <resign-game>
            || <quit>
        }

        token move-pawn  { $<move> = [ <.pawn-col> <.pawn-row> ] }
        token set-wall   { $<move> = [ <.wall-col> <.wall-row> <.wall-dir> ] }

        rule comment    { '#' <text> }
        rule leave-game { leave }
        rule quit       { quit }

        token pawn-col { <[ a .. i ]> }
        token pawn-row { <[ 1 .. 9 ]> }

        token wall-col { <[ a .. j ]> }
        token wall-row { <[ 1 .. 8 ]> }
        token wall-dir { <[ h v ]> }

        token text     { .* }
    }

    my class PlayerActions {
        has $.client;
        has $.server;

        method move-pawn($/) {
            $.server.move($.client, $/<move>);
        }

        method set-wall($/) {
            $.server.move($.client, $/<move>);
        }

        method comment($/) {
            $.server.comment($.client, $/<text>);
        }

        method leave-game($/) {
            $.server.leave-game($.client);
        }

        method quit($/) {
            $.server.quit($.client);
        }
    }

    method hello($client, $name) {
        if $!names ∋ $name {
            $client.tell-error('that name is taken');
            return;
        }

        $!names{ $name }++;
        $client.hello($name);
    }

    method comment($client, $text) {
        $client.game.comment($client, $text);
    }

    method start-game($client, Int(Cool) $players, $name) {
        if %!games{ $name } :exists {
            my $status = %!games{ $name }.status;
            $client.tell-error('that game is ' ~ $status);
            return;
        }

        my $game = Game.new(:$name, :$players);
        %!games{ $name }
    }

    method join-game($client, $number, $name) {
        unless %!games{ $name } :exists {
            $client.tell-error('no such game');
            return;
        }

        %!games{ $name }.join($client, $number);

        CATCH {
            when X::Game::Quoridor::GameError {
                $client.tell-error(.message);
            }
        }
    }

    multi method move($client, SquarePosition $move) {
        $client.game.move($client, $move);
        self.complete-game($client.game);

        CATCH {
            when X::Game::Quoridor::PlayerMistake {
                $client.tell-error(.message);
            }
        }
    }

    multi method move($client, WallPosition $move) {
        $client.game.move($client, $move);

        CATCH {
            when X::Game::Quoridor::PlayerMistake {
                $client.tell-error(.message);
            }
        }
    }

    method watch-game($client, $name) {
        unless %!games{ $name } :exists {
            $client.tell-error('no such game');
            return;
        }

        %!games{ $name }.watch($client);
    }

    method leave-game($client) {
        $client.game.leave($client);
        self.complete-game($client.game);
    }

    method complete-game($game) {
        return unless $game.finished;

        push @!finished-games,  %!games{ $game.name } :delete;
    }

    method quit($client) {
        .leave($client) with $client.game;
        $client.disconnect;

        $!names{ $client.name }--;
    }

    multi method handle-message(Client $client, Str $line) {
        my $actions = ClientActions.new(:$client, :server(self));
        ClientCommands.parse($line, :$actions);
    }

    multi method handle-message(Watcher $watcher, Str $line) {
        my $actions = WatcherActions.new(:$watcher, :server(self));
        WatcherCommands.parse($line, :$actions);
    }

    multi method handle-message(Player $player, Str $line) {
        my $actions = PlayerActions.new(:$player, :server(self));
        PlayerCommands.parse($line, :$actions);
    }

    multi method client-exit(Client $client, Str :$error) {}

    multi method client-exit(Watcher $watcher, Str :$error) {}

    multi method client-exit(Player $watcher, Str :$error) {}

    method run() {
        react {
            my $server .= IO::Socket::Async.listen($!host, $!port);
            whenever $server -> $conn {
                my $this-client = Client.new;
                my $client-msg = $conn.lines.map: -> $line {
                    ($this-client, $line);
                };

                whenever $client-msg -> ($client, $line) {
                    self.handle-message($client, $line);

                    LAST { self.client-exit($client, :error<Disconnected.>) }
                    QUIT {
                        default { self.client-exit($client, :error($_)) }
                    }
                }
            }
        }
    }
}
