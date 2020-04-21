import React from 'react';
import PropTypes from 'prop-types';

const FAQDetailInfo = ({ faq, faqs, onChange }) => (
  <div>
    <div>
      <label>
        ID
        <select
          value={faq.id}
          onChange={e => onChange(e.target.value)}
          className="form-control"
        >
          {faqs.map(faq => (
            <option value={faq.id} key={faq.id}>
              {faq.id}
            </option>
          ))}
        </select>
      </label>
    </div>
    <div>
      <label>
        Title
        <input onChange={() => {}} className="form-control" value={faq.title} />
      </label>
    </div>
    <div>
      <label>
        Question
        <input
          onChange={() => {}}
          className="form-control"
          value={faq.question}
        />
      </label>
    </div>
  </div>
);

FAQDetailInfo.propTypes = {
  faqs: PropTypes.array,
  faq: PropTypes.shape({
    id: PropTypes.number.isRequired,
    title: PropTypes.string.isRequired,
    question: PropTypes.string.isRequired,
  }).isRequired,
  onChange: PropTypes.func.isRequired,
};

export default FAQDetailInfo;
