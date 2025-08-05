import os
import time
import random
import sys
from colorama import Fore, Back, Style, init

# Initialize colorama
init(autoreset=True)

class AdvancedShellGame:
    def __init__(self):
        self.cups = []
        self.ball_position = 0
        self.player_balance = 1000
        self.round_number = 1
        self.bet = 0
        self.difficulty = 1
        self.animation_speed = 0.5
        self.shuffle_count = 3
        self.colors = [Fore.RED, Fore.GREEN, Fore.BLUE, Fore.YELLOW, Fore.MAGENTA]
        self.cup_symbols = ["●", "▲", "■", "★", "◆"]
        self.sound_effects = {
            "shuffle": "♫ ",
            "win": "🎵 ",
            "lose": "💥 ",
            "bet": "💰 "
        }

    def clear_screen(self):
        os.system('cls' if os.name == 'nt' else 'clear')

    def display_header(self):
        print(f"\n{Fore.CYAN}┌{'─'*50}┐")
        print(f"│{Back.BLACK}{Fore.WHITE}          EXTREME ADVANCED SHELL GAME           {Style.RESET_ALL}{Fore.CYAN}│")
        print(f"├{'─'*50}┤")
        print(f"│ {Fore.YELLOW}Round: {self.round_number:<5}{Fore.LIGHTMAGENTA_EX}Difficulty: {self.difficulty:<5}{Fore.LIGHTGREEN_EX}Balance: ${self.player_balance:<8}{Fore.CYAN}│")
        print(f"└{'─'*50}┘\n")

    def draw_cups(self, reveal=False):
        cup_display = []
        for i in range(3 + self.difficulty):
            if reveal and i == self.ball_position:
                cup = f"{self.colors[i]}{self.cup_symbols[i]} [BALL] {Style.RESET_ALL}"
            else:
                cup = f"{self.colors[i]}{self.cup_symbols[i]} [    ] {Style.RESET_ALL}"
            cup_display.append(cup)
        
        # Add shuffling animation effect
        if not reveal:
            for _ in range(3):
                print("\r" + " ".join(cup_display), end="")
                time.sleep(0.1)
                print("\r" + " ".join([c.replace(' [    ]', '      ') for c in cup_display]), end="")
                time.sleep(0.1)
                print("\r" + " ".join(cup_display), end="")
        
        print(" ".join(cup_display))
        
        # Draw cup numbers
        numbers = " ".join([f"   {i+1}   " for i in range(3 + self.difficulty)])
        print(f"{Fore.LIGHTWHITE_EX}{numbers}\n")

    def animate_shuffle(self):
        moves = ["L-to-R", "R-to-L", "Cross", "Rotate", "Random"]
        print(f"\n{Fore.LIGHTYELLOW_EX}Shuffling with {self.shuffle_count} {random.choice(moves)} moves...{Style.RESET_ALL}")
        
        for i in range(self.shuffle_count):
            # Choose two random cups to swap
            a, b = random.sample(range(len(self.cups)), 2)
            self.cups[a], self.cups[b] = self.cups[b], self.cups[a]
            
            # Update ball position if moved
            if self.ball_position == a:
                self.ball_position = b
            elif self.ball_position == b:
                self.ball_position = a
            
            # Visual and sound effects
            print(f"{self.sound_effects['shuffle']}Move {i+1}: Swapping cups {a+1} and {b+1}")
            self.draw_cups()
            time.sleep(self.animation_speed)
        
        # Final shuffle animation
        print(f"{Fore.LIGHTGREEN_EX}Shuffle complete!{Style.RESET_ALL}")
        self.draw_cups()

    def place_bet(self):
        print(f"\n{Fore.LIGHTCYAN_EX}Current Balance: ${self.player_balance}{Style.RESET_ALL}")
        while True:
            try:
                bet = int(input(f"{Fore.LIGHTWHITE_EX}Enter your bet (0 to quit): {Fore.YELLOW}$"))
                if bet == 0:
                    print(f"{Fore.LIGHTYELLOW_EX}Thanks for playing! Final balance: ${self.player_balance}")
                    sys.exit()
                if bet < 0:
                    print(f"{Fore.RED}Please enter a positive amount.")
                    continue
                if bet > self.player_balance:
                    print(f"{Fore.RED}Insufficient funds. Max bet: ${self.player_balance}")
                    continue
                self.bet = bet
                self.player_balance -= bet
                print(f"{self.sound_effects['bet']}{Fore.LIGHTGREEN_EX}${bet} bet placed!{Style.RESET_ALL}")
                return
            except ValueError:
                print(f"{Fore.RED}Invalid input. Please enter a number.")

    def get_guess(self):
        while True:
            try:
                guess = int(input(f"{Fore.LIGHTWHITE_EX}Where's the ball? (1-{3 + self.difficulty}): "))
                if 1 <= guess <= (3 + self.difficulty):
                    return guess - 1
                print(f"{Fore.RED}Invalid cup number. Choose 1-{3 + self.difficulty}")
            except ValueError:
                print(f"{Fore.RED}Please enter a number.")

    def reveal_and_payout(self, guess):
        print(f"\n{Fore.MAGENTA}Revealing the ball...{Style.RESET_ALL}")
        time.sleep(1)
        
        # Dramatic reveal animation
        for i in range(3):
            print("\r" + "   "*20, end="")
            time.sleep(0.2)
            self.draw_cups(reveal=True)
            time.sleep(0.3)
        
        if guess == self.ball_position:
            payout = self.bet * (2 + self.difficulty * 0.5)
            self.player_balance += payout
            print(f"{self.sound_effects['win']}{Back.GREEN}{Fore.BLACK} WINNER! {Style.RESET_ALL}{Fore.LIGHTGREEN_EX}${payout:.2f} earned!")
            print(f"{Fore.LIGHTYELLOW_EX}┌{'─'*30}┐")
            print(f"│   {Fore.CYAN}You tracked the ball perfectly!   {Fore.YELLOW}│")
            print(f"└{'─'*30}┘")
        else:
            print(f"{self.sound_effects['lose']}{Back.RED}{Fore.BLACK} LOSS! {Style.RESET_ALL}{Fore.LIGHTRED_EX}Ball was under cup {self.ball_position+1}")
            print(f"{Fore.LIGHTYELLOW_EX}┌{'─'*30}┐")
            print(f"│  {Fore.RED}The cups outsmarted you this time!  {Fore.YELLOW}│")
            print(f"└{'─'*30}┘")

    def adjust_difficulty(self):
        if self.player_balance > 1500:
            self.difficulty = min(4, self.difficulty + 1)
            self.animation_speed = max(0.1, self.animation_speed * 0.8)
            self.shuffle_count += 2
            print(f"\n{Back.BLUE}{Fore.WHITE} ADVANCED TO LEVEL {self.difficulty}! {Style.RESET_ALL}")
        elif self.player_balance < 300:
            self.difficulty = max(1, self.difficulty - 1)
            self.animation_speed = min(0.8, self.animation_speed * 1.2)
            self.shuffle_count = max(3, self.shuffle_count - 1)
            print(f"\n{Back.YELLOW}{Fore.BLACK} EASIER LEVEL {self.difficulty} {Style.RESET_ALL}")

    def play_round(self):
        self.clear_screen()
        self.display_header()
        
        # Initialize cups and ball
        self.cups = [f"Cup {i+1}" for i in range(3 + self.difficulty)]
        self.ball_position = random.randint(0, len(self.cups)-1)
        
        # Show initial position
        print(f"{Fore.LIGHTGREEN_EX}Watch carefully! The ball is under cup {self.ball_position+1}")
        self.draw_cups()
        time.sleep(1.5)
        
        # Place bet
        self.place_bet()
        
        # Shuffle cups
        self.animate_shuffle()
        
        # Get player's guess
        player_guess = self.get_guess()
        
        # Reveal results
        self.reveal_and_payout(player_guess)
        
        # Adjust difficulty for next round
        self.adjust_difficulty()
        self.round_number += 1
        
        # Pause before next round
        input(f"\n{Fore.LIGHTWHITE_EX}Press Enter to continue...")

    def start_game(self):
        print(f"\n{Back.MAGENTA}{Fore.WHITE} WELCOME TO BET SHELL GAME! ")
        print(f"{Fore.LIGHTYELLOW_EX}Track the ball under the moving cups and win big!")
        print(f"{Fore.LIGHTCYAN_EX}Difficulty increases as your balance grows. Good luck!\n")
        
        while self.player_balance > 0:
            self.play_round()
        
        print(f"{Back.RED}{Fore.WHITE} GAME OVER! You've run out of funds. ")

# Start the game
if __name__ == "__main__":
    game = AdvancedShellGame()
    game.start_game()