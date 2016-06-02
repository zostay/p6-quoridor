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

subset SquarePosition of Str where /^ <[a .. i]> <[1 .. 9]> $/;
subset WallPosition of Str where /^ <[a .. j]> <[1 .. 8]> <[h v]> $/;

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
    has SetHash $.walls = SetHash.new;

    has SetHash %.blocked;

    submethod BUILD(:$!players = 2) {
        if $!players == 2 {
            @!pawns = <e9 e1>;
        }
        elsif $!players == 4 {
            @!pawns = <e9 e1 i5 a5>;
        }
        else {
            die X::Game::Quoridor::BadNumberOfPlayers.new;
        }
    }

    method this-player() returns Int:D {
        $!turn + 1
    }

    method next-turn() {
        $!turn = ($!turn + 1) % $!players;
    }

    multi method move(Game::Quoridor::Board:D: SquarePosition $to) {
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
        self.next-turn;
    }

    multi method move(Game::Quoridor::Board:D: WallPosition $at) {
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

    method text-board(Game::Quoridor::Board:D:) {
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
