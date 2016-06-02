use v6;
use lib 'lib';
use Game::Quoridor;

sub MAIN(Int :$players = 2, Bool :$port) {
    my Game::Quoridor::Board $b .= new(:$players);

    loop {
        say $b.text-board;
        my $move = prompt "Player #{$b.this-player}> ";
        ''.say;

        given $move {
            when Game::Quoridor::SquarePosition:D { }
            when Game::Quoridor::WallPosition:D { }
            when "resign" {
                say "Player #{$b.this-player} resigns.";
                last;
            }
            default {
                say 'invalid move: try something like "e4" or "e4h" or "resign"';
                next;
            }
        }

        $b.move($move);

        CATCH {
            when X::Game::Quoridor::PlayerMistake {
                note $_.message;
            }
        }

        NEXT { ''.say }
    }
}
