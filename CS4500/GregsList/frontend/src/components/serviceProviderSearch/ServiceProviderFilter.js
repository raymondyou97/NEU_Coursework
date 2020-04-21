import React from 'react';

class ServiceProviderFilter extends React.Component {
  constructor(props) {
    super(props);

    this.newPredicates = this.props.searchPredicates;
  }

  displayFilters() {
    let searchPredicates = this.props.searchPredicates;
    let questionCount = 0;
    let finalDisplay = searchPredicates.map(predicate => {
      const question = predicate.serviceQuestion;
      questionCount++;
      let choices = question.choices.split(',');
      switch (question.type) {
        case 'MultipleChoice':
          return (
            <div key={question.id} className="service-filter-question">
              <h5>
                Question {questionCount}: {question.question}
              </h5>
              {this.getMultipleChoice(questionCount, choices, i => {
                predicate.serviceAnswer.choiceAnswer = i;
                this.newPredicates = searchPredicates;
              })}
            </div>
          );
        case 'TrueFalse':
          return (
            <div key={question.id} className="service-filter-question">
              <h5>
                Question {questionCount}: {question.question}
              </h5>
              {this.getTrueFalse(questionCount, choices, bool => {
                predicate.serviceAnswer.trueFalseAnswer = bool;
                this.newPredicates = searchPredicates;
              })}
            </div>
          );
        case 'Range':
          return (
            <div key={question.id} className="service-filter-question">
              <h5>
                Question {questionCount}: {question.question}
              </h5>
              {this.getRange(questionCount, choices, rangeVal => {
                predicate.serviceAnswer.minRangeAnswer = rangeVal;
                predicate.serviceAnswer.maxRangeAnswer = rangeVal;
                this.newPredicates = searchPredicates;
              })}
            </div>
          );
        default:
          break;
      }
      return [];
    });

    return finalDisplay;
  }

  getMultipleChoice(questionCount, choices, handleChange) {
    let finalView = [];
    for (let i = 0; i < choices.length; i++) {
      finalView.push(
        <div key={i} className="multiple-choice-option">
          <label>
            <input
              name={questionCount}
              type="radio"
              onChange={() => handleChange(i)}
            />
            &nbsp;{choices[i]}
          </label>
        </div>
      );
    }

    return finalView;
  }

  getTrueFalse(questionCount, choices, handleChange) {
    let finalView = [];
    for (let i = 0; i < choices.length; i++) {
      finalView.push(
        <span key={i} className="true-false-option">
          <label>
            <input
              name={questionCount}
              type="radio"
              onChange={() => handleChange(choices[i])}
            />
            &nbsp;{choices[i]}
          </label>
        </span>
      );
    }

    return finalView;
  }

  getRange(questionCount, choices, handleChange) {
    let min = choices[0];
    let max = choices[1];
    return (
      <div className="range-question">
        <input
          id={questionCount}
          type="range"
          className="form-control-range"
          min={min}
          max={max}
          onChange={() => {
            const currentVal = document.getElementById(questionCount).value;
            this.getCurrentRangeVal(questionCount, currentVal);
            handleChange(currentVal);
          }}
        />
        <p>
          Value: <span id={'val' + questionCount} />
        </p>
      </div>
    );
  }

  getCurrentRangeVal(questionCount, currentVal) {
    document.getElementById('val' + questionCount).innerHTML = currentVal;
  }

  render() {
    return (
      <div>
        <div className="justify-content-center pad-bottom">
          <h3>Filters</h3>
        </div>
        {this.displayFilters()}
        <button
          className="filter-button"
          onClick={() => {
            this.props.fetchFilteredServiceProviders(this.newPredicates);
          }}
        >
          Filter
        </button>
      </div>
    );
  }
}

export default ServiceProviderFilter;
