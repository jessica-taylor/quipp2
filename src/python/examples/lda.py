from quipp import *

n_classes = 10
n_words = 10000
n_words_per_document = 1000

ClassType = Categorical(n_classes)
WordType = Categorical(n_words)

class_to_word = rand_function(ClassType, WordType)

def sample():
    which_class = uniform_categorical(n_classes)
    words = [class_to_word(which_class) for i in range(n_words_per_document]
    return (which_class, words)

run_example(sample)
