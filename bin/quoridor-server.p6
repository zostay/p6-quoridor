use v6;
use lib 'lib';
use Game::Quoridor;

sub MAIN(Str :$host = 'localhost', Int :$port = 9999) {
    my $server = Game::Quoridor::Server.new(:$host, :$port);
    $server.run;
}
