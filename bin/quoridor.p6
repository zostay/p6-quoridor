use v6;
use lib 'lib';
use Game::Quoridor;

sub MAIN(Int :$players = 2, Int :$port) {
    my Game::Quoridor::Board $b .= new(:$players);

    my IO::Socket::INET $sock;
    my SetHash $remote .= new;
    my %remote-conn;
    if $port {
        for 1 .. $players -> $n {
            my $type = prompt "Is player #$n local or remote? [lr] ";
            redo unless $type.lc ~~ any('l', 'r');
            $remote{ $n }++ if $type.lc eq 'r';
        }

        if $remote.elems > 0 {
            $sock .= new(:localport($port), :listen);
            say "Waiting for bots to join...";
            while my $conn = $sock.accept {
                my $who = $conn.get;
                die "remote claims to be same as local player" unless $remote{ $who };
                die "two remotes claim to be the same player" if %remote-conn{ $who };

                %remote-conn{ $who } = $conn;

                last if %remote-conn.elems == $remote.elems;
            }
        }
    }

    loop {
        say $b.text-board;

        my $this-player = $b.this-player;

        my $move;
        if $remote{ $this-player } {
               $move    = %remote-conn{ $this-player }.get;
            my $comment = %remote-conn{ $this-player }.get;
            say "Player #$this-player> $move";
            say "Player says: $comment" if $comment;
        }
        else {
            $move = prompt "Player #$this-player> ";
            ''.say;
        }

        for %remote-conn.kv -> $that-player, $conn {
            $conn.put("$this-player $move");
        }

        given $move {
            when Game::Quoridor::SquarePosition:D { }
            when Game::Quoridor::WallPosition:D { }
            when "resign" {
                say "Player #$this-player resigns.";
                last;
            }
            when so $remote{ $this-player } {
                say "Bot #$this-player has made an illegal move. Automatically resigns.";
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
