unit module Game::Quoridor;
use v6;

my class X::Game::Quoridor is Exception {
}

my class X::Game::Quoridor::GameError is X::Game::Quoridor {
}

my class X::Game::Quoridor::WrongNumberOfPlayers is X::Game::Quoridor::GameError {
    method message() { "game error: bad number of players" }
}

my class X::Game::Quoridor::PlayerMistake is X::Game::Quoridor {
}

my class X::Game::Quoridor::GameOver is X::Game::Quoridor::PlayerMistake {
    method message() { "game over" }
}

my class X::Game::Quoridor::IllegalMove is X::Game::Quoridor::PlayerMistake {
    method message() { "illegal move" }
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

my class X::Game::Quoridor::WallCutsOff is X::Game::Quoridor::IllegalMove {
    method message() { callsame() ~ ": wall position will block a pawn from victory" }
}

my class X::Game::Quoridor::OutOfWalls is X::Game::Quoridor::IllegalMove {
    method message() { callsame() ~ ": player is out of walls" }
}

subset SquarePosition of Str where /^ <[a .. i]> <[1 .. 9]> $/;
subset WallPosition of Str where /^ <[a .. j]> <[1 .. 8]> <[h v]> $/;

my multi to-num(Str:D $x where any('a' .. 'i')) { $x.ord - 'a'.ord }
my multi to-num(Str:D $x where any('1' .. '9')) { $x - 1 }

my sub infix:<delta>(SquarePosition:D $from, SquarePosition:D $to) returns Int:D is equiv(&infix:<->) is export {
    my ($from_c, $to_c) = ($from, $to).map: { [.comb.map({ to-num($_) })] };
    [+] ($from_c.list Z- $to_c.list).map: *.abs;
}

my sub infix:<a+>(Str:D() $x where any('a' .. 'i'), Int:D $y) is equiv(&infix:<+>) is export { ($x.ord + $y).chr }
my sub infix:<a->(Str:D() $x where any('a' .. 'i'), Int:D $y) is equiv(&infix:<->) is export { ($x.ord - $y).chr }

my sub infix:<xy->(SquarePosition:D $from, SquarePosition:D $to) is equiv(&infix:<->) is export {
    my ($from_c, $to_c) = ($from, $to).map: { [.comb.map({ to-num($_) }) ]};
    $from_c »-« $to_c;
}

my sub infix:<xy+>(SquarePosition:D $from, Positional:D $to) is equiv(&infix:<+>) is export {
    my ($a, $b) = $from.comb;
    $a a+ $to[0] ~ $b + $to[1];
}

my sub neighbors(SquarePosition:D $s) is export {
    my ($a, $b) = $s.comb;
    ($a a+ 1 ~ $b, $a a- 1 ~ $b, $a ~ $b + 1, $a ~ $b - 1).grep: SquarePosition:D;
}

my sub straight-hops(SquarePosition:D $s) is export {
    my ($a, $b) = $s.comb;
    (
        # pawn here, hop here
        ($a a+ 1 ~ $b, $a a+ 2 ~ $b),
        ($a a- 1 ~ $b, $a a- 2 ~ $b),
        ($a ~ $b + 1, $a ~ $b + 2),
        ($a ~ $b + 1, $a ~ $b - 2),
    ).grep: { .[1] ~~ SquarePosition:D };
}

my sub el-hops(SquarePosition:D $s) is export {
    my ($a, $b) = $s.comb;
    (
        # pawn here, hop here, blocked by wall here
        ($a a+ 1 ~ $b, $a a+ 1 ~ $b + 1, $a a+ 2 ~ $b),
        ($a a+ 1 ~ $b, $a a+ 1 ~ $b - 1, $a a+ 2 ~ $b),
        ($a a- 1 ~ $b, $a a- 2 ~ $b + 1, $a a- 2 ~ $b),
        ($a a- 1 ~ $b, $a a- 2 ~ $b - 1, $a a- 2 ~ $b),
        ($a ~ $b + 1, $a a+ 1 ~ $b + 1, $a ~ $b + 2),
        ($a ~ $b + 1, $a a- 1 ~ $b + 1, $a ~ $b + 2),
        ($a ~ $b + 1, $a a+ 1 ~ $b - 1, $a ~ $b - 2),
        ($a ~ $b + 1, $a a- 1 ~ $b - 1, $a ~ $b - 2),
    ).grep: { .[1] ~~ SquarePosition:D };
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

my sub timethis(&code, $name) {
    my ($start, $stop);
    ENTER { $start = now }
    code();
    LEAVE {
        $stop = now;
        say "$name took " ~ $stop - $start ~ " seconds.";
    }
}

class Board {
    has $.players;

    has $.turn = 0;
    has SquarePosition @.pawns;
    has @.victory-squares;
    has @.reserve-walls;
    has SetHash $.walls .= new;

    has SetHash %.blocked;

    has @.distances;

    has Int $.winner;

    submethod BUILD(:$!players = 2) {
        @!pawns = <e9 e1>;
        @!victory-squares = (
            [ ('a' .. 'i') »~» '1' ],
            [ ('a' .. 'i') »~» '9' ],
        );
        @!reserve-walls = 10, 10;

        if $!players == 4 {
            @!pawns.append: <i5 a5>;
            @!victory-squares.push:
            [ 'a' «~« ('1' .. '9') ],
            [ 'i' «~« ('1' .. '9') ],
            ;
            @!reserve-walls = 5, 5, 5, 5;
        }

        unless $!players ~~ 2|4 {
            die X::Game::Quoridor::BadNumberOfPlayers.new;
        }

        self.calculate-distances;
    }

    method dupe() returns Board:D {
        self.clone(
            :pawns(@!pawns.clone),
            :walls(SetHash.new($!walls.keys)),
            :reserve-walls(@!reserve-walls.clone),
            :blocked(
                %!blocked.list.map({
                    .key => SetHash.new( .value.keys )
                })
            ),
        );
    }

    method real-neighbors(SquarePosition:D $sq, Set() :$exclude, :$include-opponents-of) {
        gather for neighbors($sq).grep({ not %!blocked{ $sq }{ $_ } }) {
            when $exclude { next }
            when any(|@!pawns) {
                take $_ if $include-opponents-of.defined
                        && @!pawns[ $include-opponents-of ] ne $_;

                my $vec = $_ xy- $sq;
                my $hop = $_ xy+ $vec;

                # see if either el-hop is a neighbor
                if %!blocked{ $_ }{ $hop } {
                    my $hop1 = $_ xy+ $vec.reverse;
                    my $hop2 = $_ xy+ $vec.reverse.map: -*;

                    for $hop1, $hop2 -> $el-hop {
                        next unless $el-hop ~~ SquarePosition;
                        next if %!blocked{ $_ }{ $el-hop };
                        next if $el-hop ~~ any(|@!pawns);
                        take $el-hop;
                    }
                }

                # include straight hop as neighbor
                else {
                    take $hop if $hop ~~ SquarePosition and not %!blocked{ $_ }{ $hop };
                }
            }
            default {
                take $_;
            }
        }
    }

    method open-walls() {
        set('a' .. 'h' X~ '1' .. '8' X~ 'h', 'v')
            (-) $!walls
            (-) $!walls.keys.grep(/h$/).map({ .subst(/^(.)/, { ~.[0] a+ 1 }) })
            (-) $!walls.keys.grep(/h$/).map({ .subst(/^(.)/, { ~.[0] a- 1 }) })
            (-) $!walls.keys.grep(/v$/).map({ .subst(/^(\d)/, { ~.[0] + 1 }) })
            (-) $!walls.keys.grep(/v$/).map({ .subst(/^(\d)/, { ~.[0] - 1 }) })
    }

    method calculate-distances() {
        for @!pawns.kv -> $i, $pawn {
            my @squares = $pawn => $pawn;
            my %distance;

            my $iterations = 0;
            SQUARE: while my $p = @squares.shift {
                next SQUARE with %distance{ $p.value };
                %distance{ $p.value } = $p.value eq $pawn ?? 0 !! %distance{ $p.key } + 1;
                @squares.append(
                    self.real-neighbors($p.value,
                        :exclude($pawn),
                        :include-opponents-of($i)
                    ).grep({ not %distance{ $_ }.defined })
                     .map({ $p.value => $_ })
                );
            }

            #dd %distance;
            @!distances[$i] = %distance;
        }
    }

    method this-player() returns Int:D {
        $!turn + 1
    }

    method next-turn() {
        $!turn = ($!turn + 1) % $!players;
    }

    multi method move(Board:D: SquarePosition $to) {
        die X::Game::Quoridor::GameOver.new with $!winner;
        die X::Game::Quoridor::SquareOccupied.new if $to ~~ any(|@!pawns);

        my $here := @!pawns[ $!turn ];

        my $delta = $here delta $to;

        # Moving to the same space is not allowed
        if $delta == 0 {
            die X::Game::Quoridor::NoMove.new;
        }

        # Hopping
        elsif $delta > 1 {

            # Trying a straight hop?
            if temp $_ = straight-hops($here).first({ .[1] eq $to }) {

                # There must be a pawn to hop
                die X::Game::Quoridor::IllegalHop.new
                    unless .[0] ~~ any(|@!pawns);

                # There must not be a wall blocking the hop
                die X::Game::Quoridor::BlockedBy.new(:what<wall>)
                    if %!blocked{$here}{ .[0] } or %!blocked{ .[0] }{ .[1] };
            }

            elsif temp $_ = el-hops($here).grep({ .[1] eq $to && .[0] ~~ any(|@!pawns) }) {
                dd $_;
                # There must not be a wall blocking the hop
                die X::Game::Quoridor::BlockedBy.new(:what<wall>)
                    if %!blocked{$here}{ .[0] } or %!blocked{ .[0] }{ .[1] };

                # There must be a wall or edge blocking a straight hop
                die X::Game::Quoridor::IllegalHop.new
                    unless .[2] !~~ SquarePosition or %!blocked{ .[0] }{ .[2] };
            }

            # A hop too far
            else {
                # TODO Is this right for 4-player Quoridor?

                # Nothing else is permitted
                die X::Game::Quoridor::IllegalHop.new;
            }
        }

        # A regular move
        else {

            # Can't be blocked
            die X::Game::Quoridor::BlockedBy.new(:what<wall>)
                if %!blocked{$here}{$to};

            # Can't move onto another pawn
            die X::Game::Quoridor::BlockedBy.new(:what<pawn>)
                if $to eq any(|@!pawns);
        }

        $here = $to;

        if $here ~~ any(|@!victory-squares[ $!turn ]) {
            $!winner = $!turn + 1;
            return;
        }

        self.calculate-distances;
        self.next-turn;
    }

    multi method move(Board:D: WallPosition $at) {

        die X::Game::Quoridor::GameOver.new with $!winner;
        die X::Game::Quoridor::OutOfWalls.new
            if @!reserve-walls[ $!turn ] <= 0;

        # A wall position may only be used once or walls in either direction overlap
        die X::Game::Quoridor::WallSlotOccupied.new
            if $.walls ∋ $at.subst(/.$/, 'v');
        die X::Game::Quoridor::WallSlotOccupied.new
            if $.walls ∋ $at.subst(/.$/, 'h');

        my ($c, $r, $d) = $at.comb;

        # Make sure horizontal walls don't half-overlap
        if $d eq 'h' {
            die X::Game::Quoridor::WallSlotOccupied.new
                if $.walls ∋ [~] $c a+ 1, $r, $d;
            die X::Game::Quoridor::WallSlotOccupied.new
                if $.walls ∋ [~] $c a- 1, $r, $d;
        }

        # Make sure vertical walls don't half-overlap
        else {
            die X::Game::Quoridor::WallSlotOccupied.new
                if $.walls ∋ [~] $c, $r + 1, $d;
            die X::Game::Quoridor::WallSlotOccupied.new
                if $.walls ∋ [~] $c, $r - 1, $d;
        }

        # Move is possible, set the move and the blocks list
        $.walls{ $at }++;
        my @blocks = wall-blocks($at);
        for @blocks -> $block {
            %!blocked{ $block[0] } //= SetHash.new;
            %!blocked{ $block[0] }{ $block[1] }++;
            %!blocked{ $block[1] } //= SetHash.new;
            %!blocked{ $block[1] }{ $block[0] }++;
        }

        self.calculate-distances;

        # FIXME The following breaks under certain circumstances with a 4-player
        # game. If two pawns are in a row within a corridor formed of walls on
        # either side with walls on either side of the corridor splitting the board
        # in half, the rear half of the board is temporarily unreachable because we
        # don't properly account for all possible double hops.

        # Make sure each pawn has a reachable victory squore
        my Bool @reachable = do for @!distances.keys -> $i {
            [||] @!victory-squares[$i].map: { @!distances[$i]{ $_ }.defined };
        }

        # That's illegal then, rollback and reject the move
        unless all(|@reachable) {
            $.walls{ $at }--;
            my @blocks = wall-blocks($at);
            for @blocks -> $block {
                %!blocked{ $block[0] }{ $block[1] }--;
                %!blocked{ $block[1] }{ $block[0] }--;
            }

            die X::Game::Quoridor::WallCutsOff.new;
        }

        @!reserve-walls[ $!turn ]--;
        self.next-turn;
    }

    method text-board(Game::Quoridor::Board:D:) {
        my $out = "   a b c d e f g h i\n  /-+-+-+-+-+-+-+-+-\\\n";
        for '1' .. '9' -> $r {
            $out ~= $r ~ ' |';
            for 'a' .. 'i' -> $c {
                $out ~= @!pawns.grep($c ~ $r, :k).map({ $_ + 1 }).first // ' ';

                if $c eq 'i' || $!walls ∋ $c ~ $r ~ 'v' || $!walls ∋ $c ~ $r - 1 ~ 'v' {
                    $out ~= '|';
                }
                else {
                    $out ~= ' ';
                }
            }
            $out ~= "\n";

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
