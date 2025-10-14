#include <stdio.h>
#include <stdlib.h>
#include <ncurses.h>
#include <unistd.h>
#include <time.h>

#define WIDTH 40
#define HEIGHT 20
#define MAX_SNAKE_LEN 800

typedef struct {
    int x, y;
} Point;

typedef struct {
    Point body[MAX_SNAKE_LEN];
    int length;
    int dx, dy;
} Snake;

typedef struct {
    Point pos;
} Food;

void init_game(Snake *s, Food *f) {
    s->length = 3;
    s->body[0].x = WIDTH / 2;
    s->body[0].y = HEIGHT / 2;
    s->body[1].x = WIDTH / 2 - 1;
    s->body[1].y = HEIGHT / 2;
    s->body[2].x = WIDTH / 2 - 2;
    s->body[2].y = HEIGHT / 2;
    s->dx = 1;
    s->dy = 0;
    
    f->pos.x = rand() % (WIDTH - 2) + 1;
    f->pos.y = rand() % (HEIGHT - 2) + 1;
}

void draw_border() {
    for (int i = 0; i < WIDTH; i++) {
        mvprintw(0, i, "#");
        mvprintw(HEIGHT - 1, i, "#");
    }
    for (int i = 0; i < HEIGHT; i++) {
        mvprintw(i, 0, "#");
        mvprintw(i, WIDTH - 1, "#");
    }
}

void draw_snake(Snake *s) {
    for (int i = 0; i < s->length; i++) {
        if (i == 0) {
            mvprintw(s->body[i].y, s->body[i].x, "O");
        } else {
            mvprintw(s->body[i].y, s->body[i].x, "o");
        }
    }
}

void draw_food(Food *f) {
    mvprintw(f->pos.y, f->pos.x, "*");
}

int check_collision(Snake *s) {
    Point head = s->body[0];
    
    if (head.x <= 0 || head.x >= WIDTH - 1 || head.y <= 0 || head.y >= HEIGHT - 1) {
        return 1;
    }
    
    for (int i = 1; i < s->length; i++) {
        if (head.x == s->body[i].x && head.y == s->body[i].y) {
            return 1;
        }
    }
    
    return 0;
}

void move_snake(Snake *s) {
    for (int i = s->length - 1; i > 0; i--) {
        s->body[i] = s->body[i - 1];
    }
    
    s->body[0].x += s->dx;
    s->body[0].y += s->dy;
}

void spawn_food(Food *f, Snake *s) {
    int valid;
    do {
        valid = 1;
        f->pos.x = rand() % (WIDTH - 2) + 1;
        f->pos.y = rand() % (HEIGHT - 2) + 1;
        
        for (int i = 0; i < s->length; i++) {
            if (f->pos.x == s->body[i].x && f->pos.y == s->body[i].y) {
                valid = 0;
                break;
            }
        }
    } while (!valid);
}

int main() {
    srand(time(NULL));
    
    initscr();
    cbreak();
    noecho();
    keypad(stdscr, TRUE);
    nodelay(stdscr, TRUE);
    curs_set(0);
    
    Snake snake;
    Food food;
    int score = 0;
    int ch;
    
    init_game(&snake, &food);
    
    while (1) {
        clear();
        
        draw_border();
        draw_snake(&snake);
        draw_food(&food);
        
        mvprintw(HEIGHT, 2, "Score: %d | Use arrow keys to move | Press 'q' to quit", score);
        
        refresh();
        
        ch = getch();
        if (ch == 'q' || ch == 'Q') {
            break;
        }
        
        switch (ch) {
            case KEY_UP:
                if (snake.dy == 0) {
                    snake.dx = 0;
                    snake.dy = -1;
                }
                break;
            case KEY_DOWN:
                if (snake.dy == 0) {
                    snake.dx = 0;
                    snake.dy = 1;
                }
                break;
            case KEY_LEFT:
                if (snake.dx == 0) {
                    snake.dx = -1;
                    snake.dy = 0;
                }
                break;
            case KEY_RIGHT:
                if (snake.dx == 0) {
                    snake.dx = 1;
                    snake.dy = 0;
                }
                break;
        }
        
        move_snake(&snake);
        
        if (check_collision(&snake)) {
            mvprintw(HEIGHT / 2, WIDTH / 2 - 5, "GAME OVER!");
            mvprintw(HEIGHT / 2 + 1, WIDTH / 2 - 8, "Final Score: %d", score);
            refresh();
            sleep(3);
            break;
        }
        
        if (snake.body[0].x == food.pos.x && snake.body[0].y == food.pos.y) {
            score += 10;
            snake.length++;
            spawn_food(&food, &snake);
        }
        
        usleep(100000);
    }
    
    endwin();
    return 0;
}