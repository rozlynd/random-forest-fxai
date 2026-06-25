from sklearn.datasets import load_iris
from sklearn import tree

from dt_explanation import explain


def main():
    filename = "output.txt"

    ## load data
    iris = load_iris()
    X = iris['data']
    y = iris['target']
    dt = tree.DecisionTreeClassifier(random_state=0, max_depth=2)
    dt = dt.fit(X, y)

    ## create vector
    v = X[0]

    ## create features_list
    features = "F(float, float, float, float)"

    explain("a", dt, v, verbose=True) # NB : le "a" ne veut rien dire, mais n'est pas lu dans explain.

if __name__ == "__main__":
    main()



# # Split dataset into training set and test set
# X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=0.3, random_state=1) # 70% training and 30% test

# # Create Decision Tree classifer object
# clf = DecisionTreeClassifier()

# # Train Decision Tree Classifer
# clf = clf.fit(X_train,y_train)

# # Predict the response for test dataset
# y_pred = clf.predict(X_test)
