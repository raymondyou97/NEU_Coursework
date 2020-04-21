import React from 'react';
import FAQAnswerService from '../../services/FAQAnswerService';
import FAQService from '../../services/FAQService';
import FAQAnswerRows from './FAQAnswerRows';
import { Button, Table } from 'react-bootstrap';

class FAQAnswers extends React.Component {
  constructor(props) {
    super(props);
    this.faqAnswerService = FAQAnswerService.getInstance();
    this.faqService = FAQService.getInstance();
    this.state = {
      faqAnswers: [],
      faqQuestions: [],
      selectedFAQ: '',
      newAnswer: '',
    };
  }
  componentDidMount() {
    this.faqAnswerService.findAllFAQAnswers().then(faqAnswers =>
      this.setState({
        faqAnswers,
      })
    );
    this.faqService.findAllFrequentlyAskedQuestions(0, '', '', '').then(faqs =>
      this.setState({
        faqQuestions: faqs.content,
        selectedFAQ: faqs.content[0],
      })
    );
  }

  handleQuestionChange = id => {
    let faq = this.state.faqQuestions.find(f => f.id === parseInt(id));
    this.setState({ selectedFAQ: faq });
  };

  handleAnswerChange = ans => {
    this.setState({ newAnswer: ans });
  };

  reloadFAQAnswers = () => {
    this.faqAnswerService.findAllFAQAnswers().then(faqAnswers =>
      this.setState({
        faqAnswers: faqAnswers,
      })
    );
  };

  createFAQAnswer = () => {
    // Send a create request
    this.faqAnswerService
      .createFAQAnswer(this.state.selectedFAQ.id, {
        answer: this.state.newAnswer,
      })
      .then(respData => {
        this.setState(prevState => ({
          newAnswer: '',
        }));
      })
      .then(this.reloadFAQAnswers);
  };

  deleteFAQAnswer = id => {
    this.faqAnswerService.deleteFAQAnswer(id).then(this.reloadFAQAnswers);
  };

  updateFAQAnswer = (id, data) => {
    this.faqAnswerService.updateFAQAnswer(id, data).then(this.reloadFAQAnswers);
  };

  render() {
    return (
      <div>
        <h3>FAQ Answers</h3>
        <Table bordered striped>
          <thead>
            <tr>
              <th>Title</th>
              <th>Question</th>
              <th>Answer</th>
              <th>Action(s)</th>
            </tr>
            <tr>
              <td>
                <select
                  value={this.state.selectedFAQ.id}
                  onChange={e => this.handleQuestionChange(e.target.value)}
                  className="form-control"
                >
                  {this.state.faqQuestions.map(faq => (
                    <option value={faq.id} key={faq.id}>
                      {faq.title}
                    </option>
                  ))}
                </select>
              </td>
              <td>{this.state.selectedFAQ.question}</td>
              <td>
                <input
                  type="text"
                  placeholder="Enter Answer"
                  value={this.state.newAnswer}
                  onChange={e => this.handleAnswerChange(e.target.value)}
                />
              </td>
              <td>
                <Button
                  style={{ height: 'auto' }}
                  variant="primary"
                  onClick={this.createFAQAnswer}
                >
                  Create
                </Button>
              </td>
            </tr>
          </thead>
          <tbody>
            <FAQAnswerRows
              faas={this.state.faqAnswers}
              onDelete={this.deleteFAQAnswer}
              onUpdate={this.updateFAQAnswer}
            />
          </tbody>
        </Table>
      </div>
    );
  }
}

export default FAQAnswers;
