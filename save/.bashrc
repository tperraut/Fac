# Add nano as default editor
export TERM=xterm-256color
export EDITOR=vim
export TERMINAL=terminator
export BROWSER=firefox
export MAIL42=mythom008@gmail.com
export USER42=tperraut
# Gtk themes
export GTK2_RC_FILES="$HOME/.gtkrc-2.0"
# Add user binary
PATH=$HOME/.local/bin:$PATH
# Pimp
PS1='\[\e[1;32m\][\u@\h]\[\e[m\] \[\e[1;36m\]\w\[\e[m\] \[\e[1;32m\]\$\[\e[m\] \[\e[m\]'
alias ls='ls -G --color=auto'
alias ll='ls -lGa --color=auto'
alias gccw='gcc -Wall -Werror -Wextra'
alias pdf='epdfview'
alias grep='grep --color=auto'
alias jabber='gajim'
#[ ! "$UID" = "0" ] && archbey2
