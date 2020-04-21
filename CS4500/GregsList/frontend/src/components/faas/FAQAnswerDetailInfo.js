import React from 'react';
import PropTypes from 'prop-types';

const FAQAnswerDetailInfo = ({ faqAnswer, faqAnswers, onChange }) => (
  <div>
    <div>
      <h3>FAQ Answer Details</h3>
      <label>
        ID:
        <select
          value={faqAnswer.id}
          onChange={e => onChange(e.target.value)}
          className="form-control"
        >
          {faqAnswers.map(faa => (
            <option value={faa.id} key={faa.id}>
              {faa.id}
            </option>
          ))}
        </select>
      </label>
      <div>
        <div>
          <label>
            Question:
            <input
              onChange={() => {}}
              className="form-control"
              value={faqAnswer.question}
            />
          </label>
        </div>
        <div>
          <label>
            Answer:
            <input
              onChange={() => {}}
              className="form-control"
              value={faqAnswer.answer}
            />
          </label>
        </div>
      </div>
    </div>
  </div>
);

FAQAnswerDetailInfo.propTypes = {
  faqAnswer: PropTypes.shape({
    id: PropTypes.number.isRequired,
    question: PropTypes.string.isRequired,
    answer: PropTypes.string.isRequired,
  }).isRequired,
};

export default FAQAnswerDetailInfo;
